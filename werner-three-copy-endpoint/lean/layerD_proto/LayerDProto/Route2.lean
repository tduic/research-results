import LayerDProto.Contract

/-!
# Layer D prototype, route 2′: block functionals symmetrized under `H`, on a tree grid (core Lean only)

The reformulated identity (E′) (see `../README.md`, "Route 2′") needs, for every block part and every
right coset `K r` of its fold subgroup `K` in `H`, the values `F(r t) = ⟨Y, ⊗_f ρ_f(r_s(t_{σ f}))⟩` at
the points `t` of a tree grid `R = {t : t_q = d, t₂ ∈ S1[d]}` (`d` ranges over the double cosets
`G \ S₄ / G`).

For one coset representative `r = (σ, ε, g, g')` and one `d`:

* `Y` is first brought into the axis order of `σ` (`permY`, shared by all representatives with the same `σ`):
  new axis `c` is the `Y`-axis paired with output coordinate `c`, the qubit axis stays last;
* the qubit axis is contracted at the single point `r_s(d)`, the axis of coordinate 2 against a packed table
  over `S1[d]` (digit stride `β`), the axis of coordinate 1 against a packed table over all 24 diagrams
  (stride `β |S1[d]|`);
* the axis of coordinate 0 is evaluated separately at each of the 24 diagrams `t₀` (scalar tables), giving 24
  packed numbers of `24 |S1[d]|` digits (`t₁`, `i₂`).

So no packed table has more than `24 |S1[d]| ≤ 576` digits, and the number of kernel steps is about `n²`
per contraction (the first level, at a single point, works on small integers).
-/

namespace LayerDProto

/-- `l[i]` with default, by structural recursion. (`List.getD` goes through `GetElem?` and computes the
length of the list on every access, which costs the kernel `O(length)` decidability steps each time.) -/
def nth {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, i + 1, d => nth xs i d

/-- Packed table `r[c][b] = ∑ᵢ ρ(selᵢ)[c][b] 2^(st·i)` over the selected diagram indices. -/
def rtabS (k st : Nat) (rho : List (List (List Int))) (sel : List Nat) : List (List Int) :=
  (List.range k).map fun c => (List.range k).map fun b =>
    pk st (sel.map fun s => nth (nth (nth rho s []) c []) b 0)

/-- Rows of `Y` in the order `idx` (`O(n²)` list steps). -/
def permRows (idx : List Nat) (Y : List (List Int)) : List (List Int) :=
  idx.map fun i => nth Y i []

/-- `P Y Pᵀ` for the permutation `idx` of the Kronecker index (rows, then columns via two transposes). -/
def permY (n : Nat) (idx : List Nat) (Y : List (List Int)) : List (List Int) :=
  transp n (permRows idx (transp n (permRows idx Y)))

/-- `∑_{c,b} m[c][b] V[c][b]` (`m` a scalar matrix, `V` packed). -/
def frob (m V : List (List Int)) : Int :=
  (List.zipWith dot m V).foldl (· + ·) 0

/-- The 24 matrices of a `k`-dimensional module as `k²` lists (entry `(c, b)`, row-major) of 24 values. -/
def cols (k : Nat) (rho : List (List (List Int))) : List (List Int) :=
  transp (k * k) (rho.map List.flatten)

/-- `∑ₘ vₘ 2^(st·(pₘ - 1))` over the diagrams `m` with position code `pₘ > 0` (`pₘ = 0`: not selected).
The selection is given by positions indexed by the diagram, so the 24 values are read in order (no indexing). -/
def ptab (st : Nat) (pos : List Nat) (col : List Int) : Int :=
  (List.zipWith (fun v p => match p with
    | 0 => 0
    | q + 1 => v * pow2 (st * q)) col pos).foldl (· + ·) 0

/-- Packed `k × k` table from `cols` and a position list. -/
def rtabP (k st : Nat) (cs : List (List Int)) (pos : List Nat) : List (List Int) :=
  chunks k (k * k) (cs.map (ptab st pos))

/-- Coordinate 0: `∑ₘ ⟨ρ₀(m), V⟩ 2^(st·(pₘ - 1))` (scalar tables, one per diagram, in order). -/
def finalP (st : Nat) (rho0 : List (List (List Int))) (pos : List Nat) (V : List (List Int)) : Int :=
  (List.zipWith (fun m p => match p with
    | 0 => 0
    | q + 1 => frob m V * pow2 (st * q)) rho0 pos).foldl (· + ·) 0

/-- One tree-grid contraction of the axis-permuted `Y` (axes: coordinate 0, 1, 2, qubit) as one packed number,
digit `(t₀, t₁, i₂)` at `i₂ + s1 (t₁ + 24 t₀)`. `pos = [pos₀, pos₁, pos₂, pos_q]` are position codes indexed by
diagram (`pos_c[m] = i + 1` if the representative maps the `i`-th grid value of coordinate `c` to diagram `m`);
`cs = [cols₁, cols₂, cols_q]`. -/
def tensorP2 (β s1 : Nat) (ks : List Nat) (rho0 : List (List (List Int))) (cs : List (List (List Int)))
    (pos : List (List Nat)) (Y : List (List Int)) : Int :=
  let k1 := nth ks 1 1; let k2 := nth ks 2 1; let kq := nth ks 3 1
  let V := level k1 (rtabP k1 (β * s1) (nth cs 0 []) (nth pos 1 []))
    (level k2 (rtabP k2 β (nth cs 1 []) (nth pos 2 []))
      (level kq (rtabP kq 0 (nth cs 2 []) (nth pos 3 [])) Y))
  finalP (β * 24 * s1) rho0 (nth pos 0 []) V

/-- Sum over a list of coset representatives (all with the same `σ`). -/
def sumP2 (β s1 : Nat) (ks : List Nat) (rho0 : List (List (List Int))) (cs : List (List (List Int)))
    (Y : List (List Int)) : List (List (List Nat)) → Int
  | [] => 0
  | p :: rest => tensorP2 β s1 ks rho0 cs p Y + sumP2 β s1 ks rho0 cs Y rest


/-! ## Packed first level (the qubit axis at one diagram, on packed rows of `Y`)

The rows of `Y` are kept packed over the columns (digit width `w`, `yRowsP`), so the qubit axis — the fastest
row and column digit — is contracted with `k_q` big-number products per output row instead of `n²` scalar
steps: `∑_c R_(c',c) · Q_c` with `Q_c = ∑_b T[c][b] 2^(w (k_q - 1 - b))` puts `∑_{c,b} T[c][b] Y[(c',c),(b',b)]`
at digit `b' k_q + k_q - 1`; the other digits are junk, bounded by the same `2^(w-1)`, and the useful digit is
the rounded top of each `k_q w`-bit super-digit (`topDigits`). -/

/-- Rows of `Y = Bl X Brᵀ` packed over the columns with digit width `w` (no unpacking). -/
def yRowsP (k w1 w : Nat) (X Bl Br : List (List Int)) : List Int :=
  let Xp := X.map (pk w1)
  let BX := Bl.map fun row => unpk w1 k (dot row Xp)
  let Bc := colPack k w Br
  BX.map fun row => dot row Bc

/-- The top digit (width `w`) of each of the `m` balanced super-digits of width `k w` of `P`. -/
def topDigits (w k m : Nat) (P : Int) : List Int :=
  match k with
  | 0 => []
  | 1 => unpk w m (bal (w * m) P)
  | k' + 1 =>
    (unpkN ((k' + 1) * w) m (bal ((k' + 1) * w * m) P + Int.ofNat (offs ((k' + 1) * w) m)).toNat).map
      fun D => Int.subNatNat ((D + 2 ^ (k' * w - 1)) / 2 ^ (k' * w)) (2 ^ (w - 1))

/-- First level on packed rows: the fastest axis (dimension `k`) at the scalar matrix `T`; `m = n / k`.
Returns the `m × m` scalar matrix `∑_{c,b} T[c][b] Y[(c',c),(b',b)]`. -/
def level1P (w k m : Nat) (T : List (List Int)) (rows : List Int) : List (List Int) :=
  let qs := T.map fun r => pk w r.reverse
  (chunks k rows.length rows).map fun grp => topDigits w k m (dot grp qs)

/-- The remaining three axes (coordinate 0, 1, 2 order after `permY`) for one coset representative, as one
packed number (digit `(t₀, t₁, i₂)` at `i₂ + s1 (t₁ + 24 t₀)`); `pos = [pos₀, pos₁, pos₂]`, `cs = [cols₁, cols₂]`. -/
def tensorP3 (β s1 : Nat) (ks : List Nat) (rho0 : List (List (List Int))) (cs : List (List (List Int)))
    (pos : List (List Nat)) (L : List (List Int)) : Int :=
  let k1 := nth ks 1 1; let k2 := nth ks 2 1
  let V := level k1 (rtabP k1 (β * s1) (nth cs 0 []) (nth pos 1 []))
    (level k2 (rtabP k2 β (nth cs 1 []) (nth pos 2 [])) L)
  finalP (β * 24 * s1) rho0 (nth pos 0 []) V

/-- Sum over coset representatives sharing the first level (same diagram at the qubit axis) and `σ`. -/
def sumP3 (β s1 : Nat) (ks : List Nat) (rho0 : List (List (List Int))) (cs : List (List (List Int)))
    (L : List (List Int)) : List (List (List Nat)) → Int
  | [] => 0
  | p :: rest => tensorP3 β s1 ks rho0 cs p L + sumP3 β s1 ks rho0 cs L rest

end LayerDProto
