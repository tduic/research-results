import LayerDProto.Route2

/-!
# Layer D, (E′): the checked per-part kernel computation (core Lean only)

For one block part (or one row word) and one grid value `d` (`t_q = d`), `partD` computes
`∑_{r ∈ reps} ∑_{t₀, t₁ < 24, i₂ < |S1|} F(r · (t₀, t₁, S1[i₂], d)) · 2^(β (i₂ + |S1| (t₁ + 24 t₀)))`
where `F(t) = fac · ∑_{i,j} (B_l X B_rᵀ)_{ij} ∏_f ρ_f(t_f)[i_f][j_f]` and `r · t` is the action of the
parameter `r = (σ, ε, g, g')`: `(r · t)_f = g · ε(t_{σ f}) · g'` (indices of `PERMS`).

* The rows of `Y = B_l X B_rᵀ` are kept packed over the columns (`yRows`, exact).
* The qubit axis is contracted at the diagram `m = r_s(d)` with `k_q` big-number products per row; the
  useful digit of every `k_q w`-bit super-digit is read off after an untrusted unpacking that is
  re-packed and compared (`l1Row`): the comparison, the bound `bnd` and the digit bound of the
  products make the super-digits exact (`R2Sound.lean`).
* The remaining three axes are permuted by `σ` (`permY`) and contracted against packed tables built
  from position codes computed from the parameter (`posFull`, `posGrid`); coordinate 0 is done
  diagram by diagram (`finalP`).
* Representatives are grouped by `(m, σ)` so that the first level and the permutation are computed
  once per group; the grouping is re-checked (`groupOK`).

Permutation products use packed tables (`mulNat`, `invNat`): a lookup is two big-number operations.
-/

namespace LayerDProto

/-! ## Packed permutation tables -/

/-- `∑_{a,b} MULI[a][b] · 32^(24 a + b)`. -/
def mulNat : Nat := 0x443214c74254b635cf84653a56d731d0952c0110c8573d8d8c29594ef610c012918d73e1131d0952e72b5e95635cf84443004a4424c75aad79cab4424c75a9cf6363000443216b4bda5373d8d8c10931d6a10c01292f6ad2720808510ce652d0994e95b5d8d73e113994b4242021443a5653bd9cf636302142018a53a56d73994b425ac845cf94e95b5c850806252ce64a2116b1ee52ce64a29594ef60808510dee8c18da5653bd94b399282142018a307b9ac188a4005ac845cf9cad7a54c74254b6b21173c6229001b5e72ad10931d6a2906208272b5e956b21173ce652d099cad7a54a418820845ac7b94b39928845ac7bad79cab4188a4005285a8c7b5e72ad2116b1ee290620816a4a0e64a16a31dee8c18dad2f694c0110c857ba30635285a8c7bdab49c843004a45a92839ab4bda537ba306342021443ad2f694d6a4a0e68c1ee6b085080628c1ee6b2f6ad2724a16a31c6229001bdab49ca307b9ac5a928398a418820
/-- `∑_a INVI[a] · 32^a`. -/
def invNat : Nat := 0xbc6af5a6d0a39489b64c398a320820

def pmul (a b : Nat) : Nat := (mulNat >>> (5 * (24 * a + b))) % 32
def pinv (a : Nat) : Nat := (invNat >>> (5 * a)) % 32
def peps (ε : Bool) (s : Nat) : Nat := if ε then pinv s else s

/-- A parameter `(σ, ε, g, g')` with `σ` as `[σ 0, σ 1, σ 2]`. -/
abbrev KPar := List Nat × Bool × Nat × Nat

/-- `r_s(s) = g · ε(s) · g'`. -/
def kact (p : KPar) (s : Nat) : Nat := pmul (pmul p.2.2.1 (peps p.2.1 s)) p.2.2.2
/-- `r_s⁻¹(m) = ε(g⁻¹ · m · g'⁻¹)`. -/
def kinv (p : KPar) (m : Nat) : Nat := peps p.2.1 (pmul (pmul (pinv p.2.2.1) m) (pinv p.2.2.2))

/-- `i + 1` for the first position `i` of `x` in the list (counted from `i0`), `0` if absent. -/
def idxOf1 (x : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | y :: ys, i => if x == y then i + 1 else idxOf1 x ys (i + 1)

/-- Position codes of a full coordinate (all 24 diagrams): diagram `m` is the image of grid value
`r_s⁻¹(m)`. -/
def posFull (p : KPar) : List Nat := (List.range 24).map fun m => kinv p m + 1

/-- Position codes of a coordinate whose grid is the list `g`. -/
def posGrid (p : KPar) (g : List Nat) : List Nat := (List.range 24).map fun m => idxOf1 (kinv p m) g 0

/-! ## `Y`, rows packed -/

/-- Rows of `B_l X B_rᵀ` packed over the columns (digit width `w`): `∑_j Y_ij 2^(w j)`. -/
def yRows (k w : Nat) (X Bl Br : List (List Int)) : List Int :=
  let Bc := colPack k w Br
  let Z := X.map fun row => dot row Bc
  Bl.map fun row => dot row Z

/-! ## The checked first level -/

/-- The top digit (width `w`) of a balanced super-digit of width `k w` (rounding). -/
def decodeTop (w k : Nat) (s : Int) : Int :=
  if k ≤ 1 then s else (s + pow2 ((k - 1) * w - 1)) / pow2 ((k - 1) * w)

/-- One output row of the first level: `P = ∑_c R_c Q_c`, untrusted super-digits `S` re-packed and
compared, then the top digits. -/
def l1Row (w k m bnd : Nat) (qs : List Int) (grp : List Int) : Option (List Int) :=
  let P := dot grp qs
  let S := unpk (k * w) (m + 1) P
  if pk (k * w) S == P && boundedBy bnd S then some ((S.take m).map (decodeTop w k)) else none

/-- The first level at the scalar matrix `T` (`k × k`) on packed rows (`m = n / k` outputs). -/
def level1C (w k m bnd : Nat) (T : List (List Int)) (rows : List Int) : Option (List (List Int)) :=
  (chunks k rows.length rows).mapM (l1Row w k m bnd (T.map fun r => pk w r.reverse))

/-! ## The permutation of the remaining axes -/

/-- `σ⁻¹` of a permutation of `{0, 1, 2}` given as a list. -/
def inv3 (σ : List Nat) : List Nat := [idxOf1 0 σ 0 - 1, idxOf1 1 σ 0 - 1, idxOf1 2 σ 0 - 1]

/-- The old index of every new index: new axis `c` is old axis `σ⁻¹ c` (dims `ksn`). -/
def permIdx3 (ks : List Nat) (σ : List Nat) : List Nat :=
  let fc := inv3 σ
  let a := nth ks (nth fc 0 0) 1; let b := nth ks (nth fc 1 0) 1; let c := nth ks (nth fc 2 0) 1
  (List.range (a * b * c)).map fun i =>
    let j : List Nat := [i / (b * c), i / c % b, i % c]
    (nth j (nth σ 0 0) 0 * nth ks 1 1 + nth j (nth σ 1 0) 0) * nth ks 2 1 + nth j (nth σ 2 0) 0

/-! ## Groups of representatives -/

/-- A group of representatives sharing `σ`. -/
abbrev SGroup := List Nat × List KPar
/-- A group of representatives sharing the qubit diagram `m`. -/
abbrev MGroup := Nat × List SGroup

/-- Every representative of the groups has the group's `σ` and `r_s(d) = m`. -/
def groupOK (d : Nat) (gs : List MGroup) : Bool :=
  gs.all fun mg => mg.2.all fun sg => sg.2.all fun p => p.1 == sg.1 && kact p d == mg.1

/-- The contribution of one `σ`-group (first level `L` already computed). -/
def sgroupVal (β s1 n1 : Nat) (ks : List Nat) (rhos : List (List (List (List Int))))
    (S1 : List Nat) (L : List (List Int)) (sg : SGroup) : Int :=
  let fc := inv3 sg.1
  let ksn := [nth ks (nth fc 0 0) 1, nth ks (nth fc 1 0) 1, nth ks (nth fc 2 0) 1]
  let Lσ := permY n1 (permIdx3 ks sg.1) L
  let rho0 := nth rhos (nth fc 0 0) []
  let cs := [cols (nth ksn 1 1) (nth rhos (nth fc 1 0) []), cols (nth ksn 2 1) (nth rhos (nth fc 2 0) [])]
  (sg.2.map fun p => tensorP3 β s1 ksn rho0 cs [posFull p, posFull p, posGrid p S1] Lσ).foldl (· + ·) 0

/-! ## Shape and bound checks -/

/-- `max` of a list (`0` if empty). -/
def maxNat : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxNat xs)

/-- The largest absolute entry of a list matrix. -/
def entMax (M : List (List Int)) : Nat := maxNat (M.map fun r => maxNat (r.map Int.natAbs))

/-- The largest absolute row sum of a list matrix. -/
def rowSumMax (M : List (List Int)) : Nat := maxNat (M.map sumAbs)

/-- `M` has `r` rows of length `c`. -/
def isRect (r c : Nat) (M : List (List Int)) : Bool := M.length == r && M.all fun row => row.length == c

/-- The six permutations of `{0, 1, 2}` as lists. -/
def perms3 : List (List Nat) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- The module data: four lists of 24 square matrices of the sizes `ks`. -/
def rhosOK (ks : List Nat) (rhos : List (List (List (List Int)))) : Bool :=
  rhos.length == 4 && (List.range 4).all fun f =>
    (nth rhos f []).length == 24 && (nth rhos f []).all (isRect (nth ks f 1) (nth ks f 1))

/-- Shapes and bounds for `partD`: `ks = [k₀, k₁, k₂, k_q]` positive, the module tables, `X` (`k × k`),
`B_l`, `B_r` (`n × k`), the grid (`S1` without repetitions, values `< 24`), the parameters (`g, g' < 24`,
`σ` a permutation), and the digit bounds of the first level: `|Y| ≤ y_m = rowsum(B_l) |X| rowsum(B_r)`,
`4 (k_q² t_m y_m + 1) ≤ 2^w`, `4 bnd < 2^(k_q w)`. -/
def partOK (w bnd : Nat) (ks : List Nat) (k : Nat) (X Bl Br : List (List Int))
    (rhos : List (List (List (List Int)))) (d : Nat) (S1 : List Nat) (gs : List MGroup) : Bool :=
  match ks with
  | [k0, k1, k2, kq] =>
    let n := k0 * k1 * k2 * kq
    let tm := maxNat ((nth rhos 3 []).map entMax)
    let ym := rowSumMax Bl * entMax X * rowSumMax Br
    decide (0 < k0) && decide (0 < k1) && decide (0 < k2) && decide (0 < kq) && decide (0 < w) &&
    rhosOK ks rhos && isRect k k X && isRect n k Bl && isRect n k Br &&
    decide S1.Nodup && S1.all (fun x => decide (x < 24)) && decide (d < 24) &&
    gs.all (fun mg => decide (mg.1 < 24) && mg.2.all fun sg => perms3.contains sg.1 &&
      sg.2.all fun p => decide (p.2.2.1 < 24) && decide (p.2.2.2 < 24)) &&
    decide (4 * (kq * kq * tm * ym + 1) ≤ 2 ^ w) && decide (4 * bnd < 2 ^ (kq * w))
  | _ => false

/-! ## One grid value of one part -/

/-- `∑_{r ∈ groups} ∑_{grid} F(r · t) 2^(β pos)` for one grid value `d`, or `none` if a check fails. -/
def partD (β w bnd : Nat) (ks : List Nat) (k : Nat) (X Bl Br : List (List Int)) (fac : Int)
    (rhos : List (List (List (List Int)))) (d : Nat) (S1 : List Nat) (gs : List MGroup) : Option Int :=
  if !(groupOK d gs && partOK w bnd ks k X Bl Br rhos d S1 gs) then none else
  let kq := nth ks 3 1
  let n1 := nth ks 0 1 * nth ks 1 1 * nth ks 2 1
  let Yr := yRows k w X Bl Br
  let vals := gs.mapM fun mg =>
    (level1C w kq n1 bnd (nth (nth rhos 3 []) mg.1 []) Yr).map fun L =>
      (mg.2.map (sgroupVal β S1.length n1 ks rhos S1 L)).foldl (· + ·) 0
  vals.map fun v => fac * v.foldl (· + ·) 0

/-! ## The fold subgroup: `K`-invariance of a part

For `κ = (σ, ε, g, g')` the part's functional satisfies `F ∘ κ = F` if, for integer matrices `Â_u`,
`Ĉ_u` and scales `α_u` (`u = 0, 1, 2, q`),

* (`foldTabOK`) `Â_u ρ_u(s)^{(τ)} Ĉ_u = α_u ρ_{σ⁻¹u}(r_s(s))` for all `s < 24` (`τ`: transposed);
* (`foldBOK`) with `Λ[a][i] = ∏_u Â_u[i_u][a_u]`, `Γ[b][j] = ∏_u Ĉ_u[b_u][j_u]` (after the axis
  permutation `P_σ`): `Λ P_σ B_l = B_l Qᵀ` and `Γ P_σ B_r = B_r Rᵀ` (`τ`: `Γ P_σ B_r = B_l Qᵀ`,
  `Λ P_σ B_l = B_r Rᵀ`), and `Qᵀ X^{(τ)} R = α X` with `α = ∏_u α_u`, computed here from the `α_u` and
  checked to be nonzero (`foldBOK` takes the list `α_u`, so the fold lemma needs no side condition on `α`).

All products are evaluated packed (rows of `B` with digit width `w`, digit bounds checked). -/

/-- `A B` for list matrices (`B` with `k` columns). -/
def mm (k : Nat) (A B : List (List Int)) : List (List Int) := A.map fun r => (transp k B).map (dot r)

/-- `a M`. -/
def scaleM (a : Int) (M : List (List Int)) : List (List Int) := M.map (·.map (a * ·))

/-- The fold identities of the tables: `Â_u ρ_u(s)^{(τ)} Ĉ_u = α_u ρ_{σ⁻¹u}(r_s(s))`, `s < 24`. -/
def foldTabOK (ks : List Nat) (rhos : List (List (List (List Int)))) (κ : KPar) (τ : Bool)
    (As Cs : List (List (List Int))) (als : List Int) : Bool :=
  let fc := inv3 κ.1 ++ [3]
  rhosOK ks rhos && perms3.contains κ.1 && decide (κ.2.2.1 < 24) && decide (κ.2.2.2 < 24) &&
  (List.range 4).all fun u =>
    let k := nth ks u 1
    let A := nth As u []
    let C := nth Cs u []
    nth ks (nth fc u 0) 1 == k && isRect k k A && isRect k k C &&
    (List.range 24).all fun s =>
      let R := nth (nth rhos u []) s []
      mm k (mm k A (if τ then transp k R else R)) C ==
        scaleM (nth als u 0) (nth (nth rhos (nth fc u 0) []) (kact κ s) [])

/-- The axis permutation of `permIdx3` with the qubit digit appended. -/
def permIdx4 (ks : List Nat) (σ : List Nat) : List Nat :=
  let kq := nth ks 3 1
  let idx := permIdx3 ks σ
  (List.range (idx.length * kq)).map fun i => nth idx (i / kq) 0 * kq + i % kq

/-- Apply `A` (`k × k`) on the fastest axis (size `k`) and make it the slowest:
`out[a N + x] = ∑_c A[c][a] P[x k + c]`. -/
def rotApply (k : Nat) (A : List (List Int)) (P : List Int) : List Int :=
  let ch := chunks k P.length P
  (List.range k).flatMap fun a => ch.map (dot (A.map fun r => nth r a 0))

/-- `Λ P_σ B` (packed rows): the rows of `B` packed, permuted, then the four axes folded. -/
def foldRows (w : Nat) (ks : List Nat) (σ : List Nat) (As : List (List (List Int))) (B : List (List Int)) :
    List Int :=
  let Bp := B.map (pk w)
  let P := (permIdx4 ks σ).map fun i => nth Bp i 0
  rotApply (nth ks 0 1) (nth As 0 []) (rotApply (nth ks 1 1) (nth As 1 [])
    (rotApply (nth ks 2 1) (nth As 2 []) (rotApply (nth ks 3 1) (nth As 3 []) P)))

/-- `B Qᵀ`, packed rows. -/
def mulTP (k w : Nat) (B Q : List (List Int)) : List Int := B.map fun row => dot row (colPack k w Q)

/-- The packed `B`-level checks of the fold. -/
def foldBOK (w : Nat) (ks : List Nat) (k : Nat) (X Bl Br : List (List Int)) (κ : KPar) (τ : Bool)
    (As Cs : List (List (List Int))) (als : List Int) (Q R : List (List Int)) : Bool :=
  match ks with
  | [k0, k1, k2, kq] =>
    let al := nth als 0 0 * nth als 1 0 * nth als 2 0 * nth als 3 0
    let n := k0 * k1 * k2 * kq
    let Cts := (List.range 4).map fun u => transp (nth ks u 1) (nth Cs u [])
    let LB := foldRows w ks κ.1 As Bl
    let GB := foldRows w ks κ.1 Cts Br
    let Xt := if τ then transp k X else X
    let dL := n * (entMax (nth As 0 []) * entMax (nth As 1 []) * entMax (nth As 2 []) * entMax (nth As 3 [])) *
      (entMax Bl + entMax Br)
    let dG := n * (entMax (nth Cts 0 []) * entMax (nth Cts 1 []) * entMax (nth Cts 2 []) *
      entMax (nth Cts 3 [])) * (entMax Bl + entMax Br)
    let dB := (rowSumMax Bl + rowSumMax Br) * (entMax Q + entMax R)
    let dX := rowSumMax (transp k Q) * entMax Xt * rowSumMax (transp k R) + al.natAbs * entMax X
    decide (0 < k0) && decide (0 < k1) && decide (0 < k2) && decide (0 < kq) &&
    perms3.contains κ.1 && al != 0 &&
    (List.range 3).all (fun u => nth ks (nth (inv3 κ.1) u 0) 1 == nth ks u 1) &&
    As.length == 4 && Cs.length == 4 &&
    (List.range 4).all (fun u => isRect (nth ks u 1) (nth ks u 1) (nth As u []) &&
      isRect (nth ks u 1) (nth ks u 1) (nth Cs u [])) &&
    isRect k k X && isRect n k Bl && isRect n k Br && isRect k k Q && isRect k k R &&
    decide (4 * dL < 2 ^ w) && decide (4 * dG < 2 ^ w) && decide (4 * dB < 2 ^ w) &&
    decide (4 * dX < 2 ^ w) &&
    (if τ then GB else LB) == mulTP k w Bl Q && (if τ then LB else GB) == mulTP k w Br R &&
    yRows k w Xt (transp k Q) (transp k R) == X.map (fun r => pk w (r.map (al * ·)))
  | _ => false

/-! ## The subgroup `K` and its right cosets

`K` is listed with a spanning tree over its checked generators (`closureOK`); `(κ, r) ↦ κ r` from `K × reps`
onto the family's group is checked on the enumeration `hcodes` of the group (`cosetOK`). -/

/-- `q ∘ p` for permutations of `{0, 1, 2}` as lists. -/
def comp3 (q p : List Nat) : List Nat := [nth q (nth p 0 0) 0, nth q (nth p 1 0) 0, nth q (nth p 2 0) 0]

/-- The composition of `SymWerner.mulP` on parameters: `actF (mulK p q) = actF p ∘ actF q`. -/
def mulK (p q : KPar) : KPar :=
  (comp3 q.1 p.1, xor p.2.1 q.2.1,
    if p.2.1 then pmul p.2.2.1 (pinv q.2.2.2) else pmul p.2.2.1 q.2.2.1,
    if p.2.1 then pmul (pinv q.2.2.1) p.2.2.2 else pmul q.2.2.2 p.2.2.2)

/-- A parameter of the family with bosonic list `bosL`. -/
def parIn (bosL : List Nat) (p : KPar) : Bool := perms3.contains p.1 && bosL.contains p.2.2.1 && bosL.contains p.2.2.2

/-- `Ks[0]` is the identity and `Ks[m + 1] = gens[j] ∘ Ks[i]` with `tree[m] = (j, i)`, `i ≤ m`. -/
def closureOK (bosL : List Nat) (gens Ks : List KPar) (tree : List (Nat × Nat)) : Bool :=
  Ks.length == tree.length + 1 && nth Ks 0 ([], false, 0, 0) == ([0, 1, 2], false, 0, 0) &&
  Ks.all (parIn bosL) && gens.all (parIn bosL) &&
  (List.range tree.length).all fun m =>
    decide ((nth tree m (0, 0)).2 ≤ m) && decide ((nth tree m (0, 0)).1 < gens.length) &&
    nth Ks (m + 1) ([], false, 0, 0) ==
      mulK (nth gens (nth tree m (0, 0)).1 ([], false, 0, 0)) (nth Ks (nth tree m (0, 0)).2 ([], false, 0, 0))

/-- The family's group, enumerated: `(σ, ε, g, g')` with `σ ∈ perms3`, `g, g' ∈ bosL`. -/
def hcodes (bosL : List Nat) : List KPar :=
  perms3.flatMap fun σ => [false, true].flatMap fun ε => bosL.flatMap fun g => bosL.map fun g' => (σ, ε, g, g')

/-- `hcodes[h] = Ks[i] ∘ reps[j]` for `dec[h] = (i, j)`, and `|hcodes| = |Ks| |reps|`. -/
def cosetOK (bosL : List Nat) (Ks reps : List KPar) (dec : List (Nat × Nat)) : Bool :=
  dec.length == (hcodes bosL).length && Ks.length * reps.length == (hcodes bosL).length &&
  reps.all (parIn bosL) &&
  (List.range dec.length).all fun h =>
    decide ((nth dec h (0, 0)).1 < Ks.length) && decide ((nth dec h (0, 0)).2 < reps.length) &&
    mulK (nth Ks (nth dec h (0, 0)).1 ([], false, 0, 0)) (nth reps (nth dec h (0, 0)).2 ([], false, 0, 0)) ==
      nth (hcodes bosL) h ([], false, 0, 0)

end LayerDProto
