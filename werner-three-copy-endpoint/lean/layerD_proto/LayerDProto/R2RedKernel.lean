import LayerDProto.R2AsmKernel

/-!
# Layer D, (E′): the reduced-grid checks (core Lean only)

The literal-free totals of the identity. At one grid value `d` the grid has `N = 24 · 24 · |S1|` points
(position `j = (t₀ · 24 + t₁) |S1| + i₂`). The family total `Sym_H D` is invariant under the family's
group `H`, so it is enough to know it at one position per `H`-orbit of grid points: the reduced positions
`pos` (1,142 / 2,391 / 1,142 positions for the families 31 / 22 / 13 instead of 12,096 / 25,344 / 12,096).

* `digitsAt β N pos V`: the balanced width-`β` digits of `V` at the positions `pos` (one shift and one
  `mod` each); `redVal` packs them again with width `β`. A chunk of a part claims `redVal` of its `partD`
  value (a literal of `|pos|` digits instead of `N`); the family check is the unchanged `familyZeroOK`
  (the packed sum of the claimed values is `0` and the digits fit the width).
* `posOK`, `witSlice`: every grid position `j` has a witness `h_j ∈ H` and a reduced position `c_j` with
  `h_j · gpt(j) = gpt(c_j)` (checked with `kact`; `c_j ∈ pos` through a bit mask of `pos`); the witnesses
  are packed 32 bits each and checked slice by slice.

The soundness is `R2Reduced.lean`.
-/

namespace LayerDProto

/-- The balanced width-`β` digits at the positions `pos` of a number with `N` digits. -/
def digitsAt (β N : Nat) (pos : List Nat) (V : Int) : List Int :=
  let U := (V + Int.ofNat (offs β N)).toNat
  pos.map fun j => Int.subNatNat ((U >>> (β * j)) % 2 ^ β) (2 ^ (β - 1))

/-- The reduced value of a chunk: its digits at `pos`, packed again with width `β`. -/
def redVal (β N : Nat) (pos : List Nat) (V : Int) : Int := pkB β 20 (digitsAt β N pos V)

/-- `partD` followed by `redVal`: what a reduced chunk declaration evaluates. -/
def partDR (β w bnd : Nat) (ks : List Nat) (k : Nat) (X Bl Br : List (List Int)) (fac : Int)
    (rhos : List (List (List (List Int)))) (d : Nat) (S1 : List Nat) (gs : List MGroup) (pos : List Nat) :
    Option Int :=
  (partD β w bnd ks k X Bl Br fac rhos d S1 gs).map (redVal β (24 * 24 * S1.length) pos)

/-- The bit mask `∑_{c ∈ pos} 2^c` (as an `or`). -/
def maskOf : List Nat → Nat
  | [] => 0
  | c :: l => maskOf l ||| (1 <<< c)

/-- The index coordinates `[t₀, t₁, t₂]` of grid position `j`. -/
def gridIdx (S1 : List Nat) (j : Nat) : List Nat :=
  [j / (24 * S1.length), j / S1.length % 24, nth S1 (j % S1.length) 0]

/-- The parameter of a witness code `h = g' + 24 (g + 24 (ε + 2 σ))`. -/
def witPar (h : Nat) : KPar := (nth perms3 (h / 1152) [0, 1, 2], h / 576 % 2 == 1, h / 24 % 24, h % 24)

/-- One witness `e = c + 2^15 h`: `h` is a parameter of the family, `c` a reduced position, and
`h · gpt(j) = gpt(c)`. -/
def witOK (bosL S1 : List Nat) (d N mask j e : Nat) : Bool :=
  let c := e % 32768
  let h := e / 32768
  let p := witPar h
  let t := gridIdx S1 j
  let u := gridIdx S1 c
  decide (h / 1152 < 6) && bosL.contains p.2.2.1 && bosL.contains p.2.2.2 && decide (c < N) &&
  (mask >>> c) % 2 == 1 &&
  kact p (nth t (nth p.1 0 0) 0) == nth u 0 0 && kact p (nth t (nth p.1 1 0) 0) == nth u 1 0 &&
  kact p (nth t (nth p.1 2 0) 0) == nth u 2 0 && kact p d == d

/-- The witnesses of the positions `j, …, j + n - 1`, packed in `W` with 32 bits each (least significant first). -/
def witLin (bosL S1 : List Nat) (d N mask : Nat) : Nat → Nat → Nat → Bool
  | _, 0, _ => true
  | j, n + 1, W => witOK bosL S1 d N mask j (W % 2 ^ 32) && witLin bosL S1 d N mask (j + 1) n (W >>> 32)

/-- `witLin` by halves (`f` levels): the kernel never shifts the whole packed number once per entry. -/
def witSlice (bosL S1 : List Nat) (d N mask : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, j, n, W => witLin bosL S1 d N mask j n W
  | f + 1, j, n, W => if n ≤ 8 then witLin bosL S1 d N mask j n W else
      witSlice bosL S1 d N mask f j (n / 2) (W % 2 ^ (32 * (n / 2))) &&
      witSlice bosL S1 d N mask f (j + n / 2) (n - n / 2) (W >>> (32 * (n / 2)))

/-- The reduced positions are grid positions and `mask` is their bit mask. -/
def posOK (S1 pos : List Nat) (mask : Nat) : Bool :=
  maskOf pos == mask && pos.all (fun c => decide (c < 24 * 24 * S1.length))

/-! The orbit check of a grid value is `posOK` plus one `witSlice` theorem per slice of positions (each a
separate declaration, so the kernel's cache stays small); `witSlice_cover` (`R2Reduced.lean`) turns them into
`∀ j < N, ∃ e, witOK … j e = true`. -/

end LayerDProto
