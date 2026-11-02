/-!
# Layer D prototype: kernel-evaluable packed arithmetic (core Lean only, no Mathlib)

Everything here is evaluated by the Lean kernel (`decide +kernel`), so it is written for the
kernel's cost model (measured in `../README.md`):

* every reduction step costs a few microseconds and is cached for the rest of the declaration
  (about 6 KB of memory per loop iteration), so the number of *steps* must stay small;
* `Nat.add/mul/div/mod/land/lor/xor/shiftLeft/shiftRight/pow` on literals are single GMP calls
  (`Nat.pow` only for exponents `< 2^24`), so big-number arithmetic is cheap.

Hence vectors are *packed* into one integer, `pk b [x₀, x₁, …] = x₀ + 2^b x₁ + 2^(2b) x₂ + …`,
and an identity between bounded integer vectors is checked as one identity between their packings
(`Soundness.lean`: a packing with digits `|xᵢ| < 2^b / 2` is zero only if every digit is zero).

The positive-definiteness checker `checkPD` takes an integer matrix `A`, a lower-triangular
integer matrix `W` with positive diagonal and positive integers `e`, and checks
`W A Wᵀ = diag e` row by row through the packed identities
`∑ₛ W i s · (∑ₜ A s t · Ĉ'ₜ) = eᵢ Bⁱ`, `Ĉ'ₜ = ∑ⱼ W j t Bʲ`, `B = 2^β`.
This costs `O(k²)` kernel steps (big-number products) instead of `O(k³)` scalar steps.
-/

namespace LayerDProto

/-- `2 ^ b` as an integer, computed with the kernel's GMP `Nat.pow`. -/
@[inline] def pow2 (b : Nat) : Int := Int.ofNat (2 ^ b)

/-- Truncating dot product. -/
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- Join hex chunks (least significant first, `b` bits each) into one natural number; long
literals are split because the parser is quadratic in the number of digits. -/
def joinHex (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + (joinHex b xs <<< b)

/-- Balanced residue of `P` modulo `2^b`, in `[-2^(b-1), 2^(b-1))`. -/
def bal (b : Nat) (P : Int) : Int :=
  let m := P % pow2 b
  if 2 * m < pow2 b then m else m - pow2 b

/-- `n` base-`2^b` digits of a natural number (least significant first). -/
def unpkN (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, q => (q % 2 ^ b) :: unpkN b n (q / 2 ^ b)

/-- The offset `∑ᵢ<ₙ 2^(b-1) 2^(b i)` that makes balanced digits nonnegative. -/
def offs (b n : Nat) : Nat := (2 ^ (b * n) - 1) / (2 ^ b - 1) * 2 ^ (b - 1)

/-- Unpack `n` balanced digits of width `b` (inverse of `pk` on digits `|x| < 2^(b-1)`), using only
`Nat` arithmetic on the big number (the kernel's `Int` operations cost about 15x more per digit). -/
def unpk (b n : Nat) (P : Int) : List Int :=
  (unpkN b n (P + Int.ofNat (offs b n)).toNat).map fun d => Int.subNatNat d (2 ^ (b - 1))

/-- Packing `x₀ + 2^b x₁ + 2^(2b) x₂ + ⋯`. -/
def pk (b : Nat) : List Int → Int
  | [] => 0
  | x :: xs => x + pow2 b * pk b xs

/-- Column packing of the rows `r₀, r₁, …` (each of length `k`):
entry `t` is `∑ⱼ rⱼ[t] 2^(b j)`. -/
def colPack (k b : Nat) : List (List Int) → List Int
  | [] => List.replicate k 0
  | r :: rs => List.zipWith (fun x a => x + pow2 b * a) r (colPack k b rs)

/-- `V = A Ĉ'` with `Ĉ'ₜ = ∑ⱼ W j t Bʲ`: entry `s` is `∑ₜ A s t ∑ⱼ W j t Bʲ`, so that
`dot (row i of W) V = ∑ⱼ (W A Wᵀ)ᵢⱼ Bʲ`. -/
def pdV (k β : Nat) (A W : List (List Int)) : List Int :=
  let cp := colPack k β W
  A.map fun row => dot row cp

/-- Row-by-row packed check `∑ⱼ (W A Wᵀ)ᵢⱼ Bʲ = eᵢ Bⁱ`. -/
def pdRows (β : Nat) (V : List Int) : Nat → List (List Int) → List Int → Bool
  | i, w :: W, x :: e => dot w V == x * pow2 (β * i) && pdRows β V (i + 1) W e
  | _, [], [] => true
  | _, _, _ => false

/-- Row `i` of `W` is zero after position `i` and positive at position `i`. -/
def lowerPos : Nat → List (List Int) → Bool
  | _, [] => true
  | i, r :: rs => (r.drop (i + 1)).all (· == 0) && decide (0 < r.getD i 0) && lowerPos (i + 1) rs

/-- All entries bounded in absolute value by `m`. -/
def boundedBy (m : Nat) (l : List Int) : Bool := l.all fun x => decide (x.natAbs ≤ m)

/-- The positive-definiteness certificate check: `A` is `k × k`, `W` is lower triangular with
positive diagonal, `e > 0`, the digit bound `2 (k² w² a + c) < 2^β` holds, and the packed
identity `W A Wᵀ = diag e` holds. -/
def checkPD (k β w a c : Nat) (A W : List (List Int)) (e : List Int) : Bool :=
  A.length == k && A.all (fun r => r.length == k) &&
  W.length == k && W.all (fun r => r.length == k) && e.length == k &&
  lowerPos 0 W && e.all (fun x => decide (0 < x)) &&
  A.all (boundedBy a) && W.all (boundedBy w) && boundedBy c e &&
  decide (2 * (k * k * (w * w * a) + c) < 2 ^ β) &&
  pdRows β (pdV k β A W) 0 W e

/-! ## Short-`W` variant: `W A Wᵀ` strictly diagonally dominant

With a *rounded* `W` (short entries) the product `E = W A Wᵀ` is only approximately diagonal.
Its rows are unpacked by an untrusted `unpk`, re-packed (`pk`) and compared with the packed row,
which pins the digits down; then `2 Eᵢᵢ > ∑ⱼ |Eᵢⱼ|` is checked. -/

/-- `∑ |xᵢ|`. -/
def sumAbs : List Int → Nat
  | [] => 0
  | x :: xs => x.natAbs + sumAbs xs

/-- Transpose of a list of `k`-rows. -/
def transp (k : Nat) : List (List Int) → List (List Int)
  | [] => List.replicate k []
  | r :: rs => List.zipWith List.cons r (transp k rs)

/-- Row checks of the diagonally dominant variant. -/
def ddRows (β k ed : Nat) (V : List Int) : Nat → List (List Int) → Bool
  | _, [] => true
  | i, w :: W =>
    let P := dot w V
    let E := unpk β k P
    pk β E == P && boundedBy ed E && decide ((sumAbs E : Int) < 2 * E.getD i 0) && ddRows β k ed V (i + 1) W

/-- Positive definiteness of a symmetric `A` from a lower-triangular `W` with positive diagonal and
`W A Wᵀ` strictly diagonally dominant with digit bound `2 (k² w² a + ed) < 2^β`. -/
def checkPDdd (k β w a ed : Nat) (A W : List (List Int)) : Bool :=
  A.length == k && A.all (fun r => r.length == k) && transp k A == A &&
  W.length == k && W.all (fun r => r.length == k) &&
  lowerPos 0 W && A.all (boundedBy a) && W.all (boundedBy w) &&
  decide (2 * (k * k * (w * w * a) + ed) < 2 ^ β) &&
  ddRows β k ed (pdV k β A W) 0 W

/-! ## The block matrix `X0 - sh·I` and an untrusted in-kernel Bareiss elimination -/

/-- Rows of `X0 - sh · I`. -/
def shiftDiag (sh : Int) : Nat → List (List Int) → List (List Int)
  | _, [] => []
  | i, r :: rs => (r.set i (r.getD i 0 - sh)) :: shiftDiag sh (i + 1) rs

/-- One fraction-free elimination step on the remaining rows `(a, w)` (`a` = remaining columns of
the matrix, `w` = the row of the transformation `W`), with pivot row `(p, pw)` and previous
pivot `prev`. Untrusted: `checkPD` re-verifies its output. -/
def bareissStep (prev : Int) (p pw : List Int) : List (List Int × List Int) → List (List Int × List Int)
  | [] => []
  | (a, w) :: rest =>
    let piv := p.headD 0
    let m := a.headD 0
    ((List.zipWith (fun x y => (x * piv - m * y) / prev) a p).tail,
      List.zipWith (fun x y => (x * piv - m * y) / prev) w pw) :: bareissStep prev p pw rest

/-- Fraction-free (Bareiss) elimination; returns the rows of `W` (lower triangular, `W A` upper
triangular). `fuel` = number of rows. -/
def bareissW : Nat → Int → List (List Int × List Int) → List (List Int)
  | 0, _, _ => []
  | _, _, [] => []
  | n + 1, prev, (p, pw) :: rest =>
    pw :: bareissW n (p.headD 0) (bareissStep prev p pw rest)

/-- Identity rows of size `k`. -/
def idRows (k : Nat) : List (List Int) :=
  (List.range k).map fun i => (List.range k).map fun j => if i = j then 1 else 0

/-- `W` for `A` by Bareiss elimination of `[A | I]`. -/
def bareiss (k : Nat) (A : List (List Int)) : List (List Int) :=
  bareissW k 1 (List.zip A (idRows k))

/-- `diag (W A Wᵀ)` for a Bareiss `W` and symmetric `A`: `(W A Wᵀ)ᵢᵢ = Wᵢᵢ (W A)ᵢᵢ` because
`W A` is upper and `W` lower triangular (untrusted; `checkPD` re-verifies). -/
def diagWAWt : Nat → List (List Int) → List (List Int) → List Int
  | i, wi :: W, ai :: A => (wi.getD i 0 * dot wi ai) :: diagWAWt (i + 1) W A
  | _, _, _ => []

end LayerDProto
