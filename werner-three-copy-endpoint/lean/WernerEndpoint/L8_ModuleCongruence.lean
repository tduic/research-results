import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# L8: module congruence (layer A of `exact_certificate_d5/LEAN_PLAN.md`)

`verify_d5.py` step (A) checks, for every module, the integer identities
`Γ_T(P_p) J = J π(p)` (one per permutation `p`) and `G = Jᵀ J`, and step (E) evaluates the block
functional `M_b(x) = Bᵀ (⊗_t G_t π_t(s_t)) B`. This file proves the algebra that turns those
identities into a congruence of a PSD operator:

* `congr_posSemidef`: `Bᴴ M B ⪰ 0` for `M ⪰ 0`.
* `module_congr`: `Γ J = J π  →  Jᴴ Γ J = (Jᴴ J) π`.
* `intertwine_kronecker`, `gram_kronecker`, `module_congr_kronecker`: the same for a Kronecker
  product of two factors, `module_congr_kronecker₄` for four factors (three qudit sites and the
  qubit): `(⊗J)ᴴ (⊗Γ) (⊗J) = (⊗ Jᴴ J)(⊗π)`.
* `block_congr_sum`, `block_posSemidef`: if `Γ_s J = J π_s` for every `s`, then
  `∑ x_s Bᴴ (G π_s) B = (J B)ᴴ (∑ x_s Γ_s) (J B)`, so it is PSD whenever `∑ x_s Γ_s` is.
-/

open Matrix
open scoped Kronecker

namespace WernerEndpoint

section Congruence

variable {R : Type*} [Ring R] [PartialOrder R] [StarRing R] {n m : Type*} [Fintype n] [Fintype m]

/-- **L8 (congruence).** A congruence `Bᴴ M B` of a PSD matrix `M` is PSD. -/
theorem congr_posSemidef {M : Matrix n n R} (hM : M.PosSemidef) (B : Matrix n m R) :
    (Bᴴ * M * B).PosSemidef :=
  hM.conjTranspose_mul_mul_same B

/-- **L8 (congruence), transpose form** for coefficients with trivial star (e.g. `ℝ`, `ℚ`, `ℤ`). -/
theorem transpose_congr_posSemidef [TrivialStar R] {M : Matrix n n R} (hM : M.PosSemidef)
    (B : Matrix n m R) : (Bᵀ * M * B).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hM.conjTranspose_mul_mul_same B

end Congruence

section Module

variable {R : Type*} [CommRing R] [StarRing R]

/-- **L8 (one factor).** `Γ J = J π` implies `Jᴴ Γ J = (Jᴴ J) π`. -/
theorem module_congr {m k : Type*} [Fintype m] [Fintype k] {Γ : Matrix m m R}
    {J : Matrix m k R} {π : Matrix k k R} (h : Γ * J = J * π) :
    Jᴴ * Γ * J = (Jᴴ * J) * π := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]

/-- **L8 (one factor), transpose form.** `Γ J = J π` implies `Jᵀ Γ J = (Jᵀ J) π`. -/
theorem module_congr_transpose {m k : Type*} [Fintype m] [Fintype k] {Γ : Matrix m m R}
    {J : Matrix m k R} {π : Matrix k k R} (h : Γ * J = J * π) :
    Jᵀ * Γ * J = (Jᵀ * J) * π := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]

variable {m₁ k₁ m₂ k₂ m₃ k₃ m₄ k₄ : Type*} [Fintype m₁] [Fintype k₁] [Fintype m₂] [Fintype k₂]
  [Fintype m₃] [Fintype k₃] [Fintype m₄] [Fintype k₄]

/-- The intertwining relation is stable under Kronecker products. -/
theorem intertwine_kronecker {Γ₁ : Matrix m₁ m₁ R} {J₁ : Matrix m₁ k₁ R} {π₁ : Matrix k₁ k₁ R}
    {Γ₂ : Matrix m₂ m₂ R} {J₂ : Matrix m₂ k₂ R} {π₂ : Matrix k₂ k₂ R}
    (h₁ : Γ₁ * J₁ = J₁ * π₁) (h₂ : Γ₂ * J₂ = J₂ * π₂) :
    (Γ₁ ⊗ₖ Γ₂) * (J₁ ⊗ₖ J₂) = (J₁ ⊗ₖ J₂) * (π₁ ⊗ₖ π₂) := by
  rw [← mul_kronecker_mul, h₁, h₂, mul_kronecker_mul]

/-- The Gram matrix of a Kronecker product is the Kronecker product of the Gram matrices. -/
theorem gram_kronecker (J₁ : Matrix m₁ k₁ R) (J₂ : Matrix m₂ k₂ R) :
    (J₁ ⊗ₖ J₂)ᴴ * (J₁ ⊗ₖ J₂) = (J₁ᴴ * J₁) ⊗ₖ (J₂ᴴ * J₂) := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul]

/-- **L8 (two factors).** -/
theorem module_congr_kronecker {Γ₁ : Matrix m₁ m₁ R} {J₁ : Matrix m₁ k₁ R}
    {π₁ : Matrix k₁ k₁ R} {Γ₂ : Matrix m₂ m₂ R} {J₂ : Matrix m₂ k₂ R} {π₂ : Matrix k₂ k₂ R}
    (h₁ : Γ₁ * J₁ = J₁ * π₁) (h₂ : Γ₂ * J₂ = J₂ * π₂) :
    (J₁ ⊗ₖ J₂)ᴴ * (Γ₁ ⊗ₖ Γ₂) * (J₁ ⊗ₖ J₂) = ((J₁ᴴ * J₁) ⊗ₖ (J₂ᴴ * J₂)) * (π₁ ⊗ₖ π₂) := by
  rw [module_congr (intertwine_kronecker h₁ h₂), gram_kronecker]

/-- **L8 (four factors: three qudit sites and the qubit).**
`(J₁⊗J₂⊗J₃⊗J₄)ᴴ (Γ₁⊗Γ₂⊗Γ₃⊗Γ₄) (J₁⊗J₂⊗J₃⊗J₄) = (G₁⊗G₂⊗G₃⊗G₄)(π₁⊗π₂⊗π₃⊗π₄)`
with `G_t = J_tᴴ J_t`. -/
theorem module_congr_kronecker₄ {Γ₁ : Matrix m₁ m₁ R} {J₁ : Matrix m₁ k₁ R}
    {π₁ : Matrix k₁ k₁ R} {Γ₂ : Matrix m₂ m₂ R} {J₂ : Matrix m₂ k₂ R} {π₂ : Matrix k₂ k₂ R}
    {Γ₃ : Matrix m₃ m₃ R} {J₃ : Matrix m₃ k₃ R} {π₃ : Matrix k₃ k₃ R}
    {Γ₄ : Matrix m₄ m₄ R} {J₄ : Matrix m₄ k₄ R} {π₄ : Matrix k₄ k₄ R}
    (h₁ : Γ₁ * J₁ = J₁ * π₁) (h₂ : Γ₂ * J₂ = J₂ * π₂) (h₃ : Γ₃ * J₃ = J₃ * π₃)
    (h₄ : Γ₄ * J₄ = J₄ * π₄) :
    (J₁ ⊗ₖ J₂ ⊗ₖ J₃ ⊗ₖ J₄)ᴴ * (Γ₁ ⊗ₖ Γ₂ ⊗ₖ Γ₃ ⊗ₖ Γ₄) * (J₁ ⊗ₖ J₂ ⊗ₖ J₃ ⊗ₖ J₄) =
      ((J₁ᴴ * J₁) ⊗ₖ (J₂ᴴ * J₂) ⊗ₖ (J₃ᴴ * J₃) ⊗ₖ (J₄ᴴ * J₄)) * (π₁ ⊗ₖ π₂ ⊗ₖ π₃ ⊗ₖ π₄) := by
  rw [module_congr (intertwine_kronecker (intertwine_kronecker (intertwine_kronecker h₁ h₂) h₃) h₄),
    gram_kronecker, gram_kronecker, gram_kronecker]

/-- **L8 (block functional).** If `Γ s * J = J * π s` for every `s ∈ S`, then the block value
`∑ x_s Bᴴ (G π_s) B` (with `G = Jᴴ J`) is the congruence `(J B)ᴴ (∑ x_s Γ_s) (J B)`. -/
theorem block_congr_sum {ι : Type*} (S : Finset ι) (x : ι → R) {m k k' : Type*} [Fintype m]
    [Fintype k] (Γ : ι → Matrix m m R) (J : Matrix m k R) (π : ι → Matrix k k R)
    (B : Matrix k k' R) (h : ∀ s ∈ S, Γ s * J = J * π s) :
    ∑ s ∈ S, x s • (Bᴴ * ((Jᴴ * J) * π s) * B) = (J * B)ᴴ * (∑ s ∈ S, x s • Γ s) * (J * B) := by
  rw [conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← module_congr (h s hs)]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- **L8 (block positivity).** Under the intertwining relations, the block value is PSD as soon as
the operator `∑ x_s Γ_s` it compresses is PSD. -/
theorem block_posSemidef [PartialOrder R] {ι : Type*} (S : Finset ι) (x : ι → R)
    {m k k' : Type*} [Fintype m] [Fintype k] [Fintype k'] (Γ : ι → Matrix m m R)
    (J : Matrix m k R) (π : ι → Matrix k k R) (B : Matrix k k' R)
    (h : ∀ s ∈ S, Γ s * J = J * π s) (hY : (∑ s ∈ S, x s • Γ s).PosSemidef) :
    (∑ s ∈ S, x s • (Bᴴ * ((Jᴴ * J) * π s) * B)).PosSemidef := by
  rw [block_congr_sum S x Γ J π B h]
  exact hY.conjTranspose_mul_mul_same (J * B)

end Module

end WernerEndpoint

#print axioms WernerEndpoint.congr_posSemidef
#print axioms WernerEndpoint.transpose_congr_posSemidef
#print axioms WernerEndpoint.module_congr
#print axioms WernerEndpoint.module_congr_transpose
#print axioms WernerEndpoint.intertwine_kronecker
#print axioms WernerEndpoint.gram_kronecker
#print axioms WernerEndpoint.module_congr_kronecker
#print axioms WernerEndpoint.module_congr_kronecker₄
#print axioms WernerEndpoint.block_congr_sum
#print axioms WernerEndpoint.block_posSemidef
