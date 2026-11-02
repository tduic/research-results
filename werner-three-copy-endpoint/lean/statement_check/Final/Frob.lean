import Mathlib.Analysis.Matrix
open Matrix
/-- Σ_ij |M_ij|² is the square of Mathlib's Frobenius norm. -/
theorem fro_eq_frobenius {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    (∑ i, ∑ j, ‖M i j‖ ^ 2) = (@Norm.norm _ (Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℂ)).toNorm M) ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  have h0 : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num
#print axioms fro_eq_frobenius
