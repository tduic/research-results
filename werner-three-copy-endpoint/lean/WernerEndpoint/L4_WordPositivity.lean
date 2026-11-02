import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# L4: word positivity (layer A of `exact_certificate_d5/LEAN_PLAN.md`)

Operators on a tensor product `⊗_{r ∈ κ} 𝕜^{ι r}` are matrices indexed by multi-indices
`x : (r : κ) → ι r`. The partial transpose `Γ_T` on the factors `r ∈ T` swaps the row and column
digit of every factor in `T`.

* `prodVec v` is the product vector `⊗_r v r`; `prodOp P` is the product operator `⊗_r P r`.
* `ptrans_vecMulVec_prodVec`: `Γ_T(|⊗v⟩⟨⊗w|) = |⊗v'⟩⟨⊗w'|` where the factors in `T` are swapped
  and conjugated (`v'_r = conj w_r`, `w'_r = conj v_r` for `r ∈ T`).
* **L4** `ptrans_prodOp_rankOne_posSemidef`: `Γ_T(⊗_r |v_r⟩⟨v_r|) ⪰ 0` — it is the rank-one
  operator of the vector whose factors in `T` are conjugated.
* General form `ptrans_prodOp_posSemidef` (over `RCLike`): `Γ_T(⊗_r P_r) ⪰ 0` for any family of
  PSD `P_r`, since `Γ_T(⊗ P_r) = ⊗ (P_r or P_rᵀ)` and Kronecker products of PSD matrices are PSD
  (`prodOp_posSemidef`).
-/

open Matrix
open scoped ComplexOrder

namespace WernerEndpoint

/-- The product vector `⊗_r v r`, as a function of the multi-index. -/
def prodVec {κ : Type*} [Fintype κ] {ι : κ → Type*} {R : Type*} [CommMonoid R]
    (v : (r : κ) → ι r → R) (x : (r : κ) → ι r) : R :=
  ∏ r, v r (x r)

/-- The product operator `⊗_r P r`. -/
def prodOp {κ : Type*} [Fintype κ] {ι : κ → Type*} {R : Type*} [CommMonoid R]
    (P : (r : κ) → Matrix (ι r) (ι r) R) : Matrix ((r : κ) → ι r) ((r : κ) → ι r) R :=
  Matrix.of fun x y => ∏ r, P r (x r) (y r)

/-- The partial transpose `Γ_T` on the tensor factors in `T`. -/
def ptrans {κ : Type*} [DecidableEq κ] {ι : κ → Type*} {R : Type*} (T : Finset κ)
    (A : Matrix ((r : κ) → ι r) ((r : κ) → ι r) R) : Matrix ((r : κ) → ι r) ((r : κ) → ι r) R :=
  Matrix.of fun x y =>
    A (fun r => if r ∈ T then y r else x r) (fun r => if r ∈ T then x r else y r)

section Algebra

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} {R : Type*} [CommRing R] [StarRing R]

/-- `⊗_r |v_r⟩⟨w_r| = |⊗v⟩⟨⊗w|`. -/
theorem prodOp_vecMulVec (v w : (r : κ) → ι r → R) :
    prodOp (fun r => vecMulVec (v r) (star (w r))) = vecMulVec (prodVec v) (star (prodVec w)) := by
  ext x y
  simp only [prodOp, prodVec, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_prod,
    Finset.prod_mul_distrib]

/-- The partial transpose of a rank-one product operator is the rank-one operator of the vectors
whose factors in `T` are exchanged and conjugated. -/
theorem ptrans_vecMulVec_prodVec [DecidableEq κ] (T : Finset κ) (v w : (r : κ) → ι r → R) :
    ptrans T (vecMulVec (prodVec v) (star (prodVec w))) =
      vecMulVec (prodVec fun r => if r ∈ T then star (w r) else v r)
        (star (prodVec fun r => if r ∈ T then star (v r) else w r)) := by
  ext x y
  simp only [ptrans, prodVec, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  by_cases h : r ∈ T
  · simp only [if_pos h, Pi.star_apply, star_star]
    ring
  · simp only [if_neg h]

/-- **L4 (rank-one form).** `Γ_T(⊗_r |v_r⟩⟨v_r|) ⪰ 0`. -/
theorem ptrans_prodOp_rankOne_posSemidef [DecidableEq κ] [∀ r, Fintype (ι r)] [PartialOrder R]
    [StarOrderedRing R] (T : Finset κ) (v : (r : κ) → ι r → R) :
    (ptrans T (prodOp fun r => vecMulVec (v r) (star (v r)))).PosSemidef := by
  rw [prodOp_vecMulVec, ptrans_vecMulVec_prodVec]
  exact posSemidef_vecMulVec_self_star _

/-- `Γ_T(⊗_r P_r) = ⊗_r (P_rᵀ if r ∈ T else P_r)`. -/
theorem ptrans_prodOp [DecidableEq κ] (T : Finset κ) (P : (r : κ) → Matrix (ι r) (ι r) R) :
    ptrans T (prodOp P) = prodOp fun r => if r ∈ T then (P r)ᵀ else P r := by
  ext x y
  simp only [ptrans, prodOp, Matrix.of_apply]
  refine Finset.prod_congr rfl fun r _ => ?_
  by_cases h : r ∈ T
  · simp only [if_pos h, Matrix.transpose_apply]
  · simp only [if_neg h]

/-- `(⊗A)(⊗B) = ⊗(A B)`. -/
theorem prodOp_mul [DecidableEq κ] [∀ r, Fintype (ι r)] (A B : (r : κ) → Matrix (ι r) (ι r) R) :
    prodOp A * prodOp B = prodOp fun r => A r * B r := by
  ext x y
  simp only [prodOp, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- `(⊗B)ᴴ = ⊗(Bᴴ)`. -/
theorem prodOp_conjTranspose (B : (r : κ) → Matrix (ι r) (ι r) R) :
    (prodOp B)ᴴ = prodOp fun r => (B r)ᴴ := by
  ext x y
  simp only [prodOp, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

end Algebra

section RCLike

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ r, Fintype (ι r)]
  {𝕜 : Type*} [RCLike 𝕜]

open scoped MatrixOrder in
/-- A Kronecker (tensor) product of PSD matrices is PSD. -/
theorem prodOp_posSemidef {P : (r : κ) → Matrix (ι r) (ι r) 𝕜} (hP : ∀ r, (P r).PosSemidef) :
    (prodOp P).PosSemidef := by
  classical
  have hfac : ∀ r, ∃ B : Matrix (ι r) (ι r) 𝕜, P r = star B * B := fun r =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hP r).nonneg
  choose B hB using hfac
  have hP' : prodOp P = (prodOp B)ᴴ * prodOp B := by
    rw [prodOp_conjTranspose, prodOp_mul]
    congr 1
    funext r
    rw [hB r, Matrix.star_eq_conjTranspose]
  rw [hP']
  exact posSemidef_conjTranspose_mul_self _

/-- **L4 (general form).** The partial transpose `Γ_T(⊗_r P_r)` of a tensor product of PSD
matrices is PSD. -/
theorem ptrans_prodOp_posSemidef (T : Finset κ) {P : (r : κ) → Matrix (ι r) (ι r) 𝕜}
    (hP : ∀ r, (P r).PosSemidef) : (ptrans T (prodOp P)).PosSemidef := by
  rw [ptrans_prodOp]
  refine prodOp_posSemidef fun r => ?_
  show (if r ∈ T then (P r)ᵀ else P r).PosSemidef
  split_ifs
  · exact (hP r).transpose
  · exact hP r

end RCLike

end WernerEndpoint

#print axioms WernerEndpoint.prodOp_vecMulVec
#print axioms WernerEndpoint.ptrans_vecMulVec_prodVec
#print axioms WernerEndpoint.ptrans_prodOp_rankOne_posSemidef
#print axioms WernerEndpoint.ptrans_prodOp
#print axioms WernerEndpoint.prodOp_mul
#print axioms WernerEndpoint.prodOp_conjTranspose
#print axioms WernerEndpoint.prodOp_posSemidef
#print axioms WernerEndpoint.ptrans_prodOp_posSemidef
