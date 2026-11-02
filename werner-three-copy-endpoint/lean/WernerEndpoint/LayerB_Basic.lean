import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul

/-!
# Layer B, shared definitions (`exact_certificate_d5/LEAN_PLAN.md`)

* `frobSq M = ∑ᵢⱼ ‖M i j‖²` — the squared Frobenius norm (a real number).
* `vnormSq v = ∑ᵢ ‖v i‖²` — the squared Euclidean norm of a vector (a real number).
* `nsqC v = ∑ᵢ conj (v i) * v i` — the same quantity as a complex number (`ofReal_vnormSq`).
* Small algebraic helpers used by L1–L3: `ofReal_norm_sq`, `mul_sum_sum`,
  `trace_mul_vecMulVec_star` (`tr(M |u⟩⟨u|) = ⟨u, M u⟩`) and `sum_sum_update`
  (averaging over one coordinate of a multi-index).
-/

open Matrix

noncomputable section

namespace WernerEndpoint

/-- The squared Frobenius norm `‖M‖²_F = ∑ᵢⱼ |M i j|²`. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- The squared Euclidean norm `‖v‖² = ∑ᵢ |v i|²`. -/
def vnormSq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- `‖v‖²` computed in `ℂ`: `∑ᵢ conj (v i) * v i`. -/
def nsqC {n : Type*} [Fintype n] (v : n → ℂ) : ℂ :=
  ∑ i, star (v i) * v i

theorem star_ofReal' (t : ℝ) : star (t : ℂ) = t := by
  exact Complex.conj_ofReal t

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = star w * w := by
  rw [Complex.ofReal_pow]; exact (Complex.conj_mul' w).symm

theorem ofReal_norm_sq' (w : ℂ) : ((‖w‖ : ℂ)) ^ 2 = star w * w := by
  rw [← Complex.ofReal_pow, ofReal_norm_sq]

theorem ofReal_vnormSq {n : Type*} [Fintype n] (v : n → ℂ) : ((vnormSq v : ℝ) : ℂ) = nsqC v := by
  simp only [vnormSq, nsqC, Complex.ofReal_sum, ofReal_norm_sq]

theorem ofReal_frobSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ((frobSq M : ℝ) : ℂ) = ∑ i, ∑ j, star (M i j) * M i j := by
  simp only [frobSq, Complex.ofReal_sum, ofReal_norm_sq]

theorem frobSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem vnormSq_nonneg {n : Type*} [Fintype n] (v : n → ℂ) : 0 ≤ vnormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `(∑ₐ f a) (∑_b g b) = ∑ₐ ∑_b f a g b`, with the first index outermost. -/
theorem mul_sum_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → ℂ) (g : β → ℂ) :
    (∑ a, f a) * (∑ b, g b) = ∑ a, ∑ b, f a * g b := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- `tr (M |u⟩⟨u|) = ⟨u | M u⟩ = star u ⬝ᵥ (M *ᵥ u)`. -/
theorem trace_mul_vecMulVec_star {n : Type*} [Fintype n] (M : Matrix n n ℂ) (u : n → ℂ) :
    (M * vecMulVec u (star u)).trace = star u ⬝ᵥ (M *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
   Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A sum over an empty type vanishes; stated through the cardinality. -/
theorem sum_eq_zero_of_card {Y : Type*} [Fintype Y] (f : Y → ℂ)
    (h : (Fintype.card Y : ℂ) = 0) : ∑ y, f y = 0 := by
  have hc : Fintype.card Y = 0 := by exact_mod_cast h
  haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hc
  simp

/-- Averaging over one coordinate: `∑_X ∑_y F (X[r ↦ y]) = |Y| · ∑_X F X`. -/
theorem sum_sum_update {R Y : Type*} [Fintype R] [DecidableEq R] [Fintype Y]
    (F : (R → Y) → ℂ) (r : R) :
    ∑ X, ∑ y, F (Function.update X r y) = (Fintype.card Y : ℂ) * ∑ X, F X := by
  let σ : (R → Y) × Y ≃ (R → Y) × Y :=
    { toFun := fun p => (Function.update p.1 r p.2, p.1 r)
      invFun := fun p => (Function.update p.1 r p.2, p.1 r)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  calc ∑ X, ∑ y, F (Function.update X r y)
      = ∑ p : (R → Y) × Y, F (σ p).1 :=
        (Fintype.sum_prod_type' (fun X y => F (Function.update X r y))).symm
    _ = ∑ p : (R → Y) × Y, F p.1 := σ.sum_comp (fun p => F p.1)
    _ = ∑ X, ∑ _y : Y, F X := Fintype.sum_prod_type' (fun X _ => F X)
    _ = (Fintype.card Y : ℂ) * ∑ X, F X := by simp [Finset.mul_sum]

end WernerEndpoint

end

#print axioms WernerEndpoint.ofReal_norm_sq
#print axioms WernerEndpoint.ofReal_vnormSq
#print axioms WernerEndpoint.ofReal_frobSq
#print axioms WernerEndpoint.trace_mul_vecMulVec_star
#print axioms WernerEndpoint.sum_sum_update
