import LayerDProto.Packed

/-!
# Layer D prototype: the block functionals in packed tuple space (core Lean only)

For a block with modules `f₁, f₂, f₃` (sites) and `f₄` (qubit) of dimensions `k₁ … k₄`
(`n = k₁k₂k₃k₄`), basis `B` (`n × k`) and multiplier `X` (`k × k`), the verifier's tuple-space
functional is `F[t] = ⟨Y, ⊗_f ρ_f(t_f)⟩`, `Y = B X Bᵀ`, `ρ_f(s) = G_f π_f(s)`, for the
`24⁴ = 331 776` diagram tuples `t`. Here the whole tensor is computed as ONE packed integer
`P = ∑_t F[t] 2^(D·t)` (digit width `D` bits, `t = ((t₁·24 + t₂)·24 + t₃)·24 + t₄`) by four
levels of packed products, one per mode, innermost (qubit) mode first:

`A₃ = ∑_{c₄,b₄} r₄(c₄,b₄) Y[…]`, `A₂ = ∑ r₃ A₃`, `A₁ = ∑ r₂ A₂`, `P = ∑ r₁ A₁`,
`r_f(c,b) = ∑_s ρ_f(s)[c][b] 2^(D·24^(4-f)·s)`.

The number of kernel steps is about `n²` (one product per entry of `Y`), not `24⁴ n²`.
`Y` itself is computed with packed rows (`O(nk)` steps) and unpacked (`n²` digits).
-/

namespace LayerDProto

/-- Consecutive chunks of length `k` (`fuel` ≥ number of chunks). -/
def chunks {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, l@(_ :: _) => l.take k :: chunks k f (l.drop k)

/-- Elementwise sum of a list of equally long lists. -/
def sumRows : List (List Int) → List Int
  | [] => []
  | [r] => r
  | r :: rs => List.zipWith (· + ·) r (sumRows rs)

/-- One contraction level: rows indexed by `(c', c_f)` (`c_f` fastest), entries by `(b', b_f)`;
`r` is the `k × k` table of packed coefficients. Output rows `c'`, entries `b'`:
`∑_{c_f,b_f} r[c_f][b_f] · rows[(c', c_f)][(b', b_f)]`. -/
def level (k : Nat) (r : List (List Int)) (rows : List (List Int)) : List (List Int) :=
  (chunks k rows.length rows).map fun grp =>
    sumRows (List.zipWith (fun row rc => (chunks k row.length row).map fun bg => dot rc bg) grp r)

/-- Packed coefficient table `r[c][b] = ∑_s ρ(s)[c][b] 2^(b·s)` from the 24 matrices `ρ(s)`. -/
def rtab (k : Nat) (stride : Nat) (rho : List (List (List Int))) : List (List Int) :=
  (List.range k).map fun c => (List.range k).map fun b =>
    pk stride (rho.map fun m => (m.getD c []).getD b 0)

/-- `Y = Bl X Brᵀ` (rows unpacked), via packed rows: `(Bl X)` with digit width `w1`, `Y` rows with
digit width `w2`. `Bl`, `Br` are `n × k`. -/
def yMat (n k w1 w2 : Nat) (X Bl Br : List (List Int)) : List (List Int) :=
  let Xp := X.map (pk w1)
  let BX := Bl.map fun row => unpk w1 k (dot row Xp)
  let Bc := colPack k w2 Br
  BX.map fun row => unpk w2 n (dot row Bc)

/-- The packed tuple tensor of one block part: modules `ρ₁ … ρ₄` (dims `k₁ … k₄`), digit width `D`. -/
def tensorP (D : Nat) (ks : List Nat) (rhos : List (List (List (List Int)))) (Y : List (List Int)) : Int :=
  let k1 := ks.getD 0 1; let k2 := ks.getD 1 1; let k3 := ks.getD 2 1; let k4 := ks.getD 3 1
  let r4 := rtab k4 D (rhos.getD 3 [])
  let r3 := rtab k3 (D * 24) (rhos.getD 2 [])
  let r2 := rtab k2 (D * 576) (rhos.getD 1 [])
  let r1 := rtab k1 (D * 13824) (rhos.getD 0 [])
  ((level k1 r1 (level k2 r2 (level k3 r3 (level k4 r4 Y)))).headD []).headD 0

end LayerDProto

namespace LayerDProto

/-! ## Scatter primitive (measurement): unpack a packed tensor into a balanced tree and gather -/

/-- Binary tree of digits. -/
inductive Tr where
  | leaf (v : Int)
  | node (l r : Tr)

/-- Unpack `2^d` balanced digits of width `D` into a tree (divide and conquer). -/
def build (D : Nat) : Nat → Int → Tr
  | 0, P => .leaf P
  | d + 1, P =>
    let lo := bal (D * 2 ^ d) P
    .node (build D d lo) (build D d ((P - lo) / pow2 (D * 2 ^ d)))

/-- Digit `i` of a depth-`d` tree. -/
def look : Nat → Tr → Nat → Int
  | _, .leaf v, _ => v
  | d + 1, .node l r, i => if i < 2 ^ d then look d l i else look d r (i - 2 ^ d)
  | 0, .node _ _, _ => 0

/-- Sum of the digits at the given positions. -/
def gather (d : Nat) (t : Tr) : List Nat → Int
  | [] => 0
  | i :: is => look d t i + gather d t is

end LayerDProto
