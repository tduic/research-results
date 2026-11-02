import Mathlib.LinearAlgebra.Matrix.Rank
import WernerEndpoint.L1_FourReplica
import WernerEndpoint.L2_Lift
import WernerEndpoint.L5_Tables

/-!
# Layer B, assembled: from rank `≤ 2` to the lifted four-replica moment

* `qfun_nonneg_of_normalized`: by homogeneity (`qfun_smul`) it suffices to prove `q ≥ 0` for
  rank-`≤ 2` operators with `‖C‖²_F = 1/2` (the case `C = 0` is `qfun_zero`).
* `qfun_nonneg_of_trace_nonneg`: if `Re Tr[objective4 · Y31] ≥ 0` for every lifted pair
  (`Tr_H |a⟩⟨a| = I/2`, `‖a‖ = ‖b‖ = 1`), then `q(C) ≥ 0` for every rank-`≤ 2` `C` on
  `ℂ^{κ → ι}` (`|ι|^{|κ|} ≥ 2`).  Layers C and D discharge the hypothesis: the certificate
  writes `Tr[objective4 · Y31]` as a sum of PSD pairings plus multiples of rows that vanish by L3.
-/

open Matrix

noncomputable section

namespace WernerEndpoint

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- The layer-B moments are the `Y31`, `Y22`, `Y13` of `L5_Tables.lean` (one copy `ι := (κ → ι) × ρ`). -/
theorem moment_eq_Y31 {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (a b : (κ → ι) × ρ → ℂ) :
    moment ![a, a, a, b] = Y31 a b := rfl

theorem moment_eq_Y22 {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (a b : (κ → ι) × ρ → ℂ) :
    moment ![a, a, b, b] = Y22 a b := rfl

theorem moment_eq_Y13 {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (a b : (κ → ι) × ρ → ℂ) :
    moment ![b, b, b, a] = Y13 a b := rfl

theorem rank_smul_le' {n : Type*} [Fintype n] [DecidableEq n] (t : ℂ) (C : Matrix n n ℂ) :
    (t • C).rank ≤ C.rank := by
  have h : t • C = (t • (1 : Matrix n n ℂ)) * C := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h]
  exact Matrix.rank_mul_le_right _ _

/-- **L2 (scaling).** It suffices to prove `q ≥ 0` for rank-`≤ 2` `C` with `‖C‖²_F = 1/2`. -/
theorem qfun_nonneg_of_normalized
    (h : ∀ C : Matrix (κ → ι) (κ → ι) ℂ, C.rank ≤ 2 → frobSq C = 1 / 2 → 0 ≤ qfun C)
    (C : Matrix (κ → ι) (κ → ι) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  rcases (frobSq_nonneg C).lt_or_eq with hpos | hzero
  · have hN : frobSq C ≠ 0 := hpos.ne'
    have hlt : (0 : ℝ) < 1 / (2 * frobSq C) := by
      apply div_pos one_pos
      linarith
    have hle : (0 : ℝ) ≤ 1 / (2 * frobSq C) := hlt.le
    set t : ℝ := Real.sqrt (1 / (2 * frobSq C)) with ht_def
    have htp : 0 < t := Real.sqrt_pos.mpr hlt
    have ht2 : t ^ 2 * frobSq C = 1 / 2 := by
      rw [ht_def, Real.sq_sqrt hle]
      field_simp
    have hnt : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hC' := h ((t : ℂ) • C) ((rank_smul_le' _ C).trans hC) (by rw [frobSq_smul, hnt, ht2])
    rw [qfun_smul, hnt] at hC'
    have htp2 : 0 < t ^ 2 := pow_pos htp 2
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos htp2 (neg_pos.mpr hneg)]
  · have hC0 : C = 0 := by
      ext i j
      have h1 : ∑ i, ∑ j, ‖C i j‖ ^ 2 = 0 := hzero.symm
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖C i j‖)).mp h1 i (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖C i j‖)).mp h2 j (Finset.mem_univ _)
      simpa using h3
    rw [hC0, qfun_zero]

/-- **Layer B reduction.** If the objective word has nonnegative expectation on every lifted
four-replica moment `Y31 = |a a a b⟩⟨a a a b|` (`Tr_H |a⟩⟨a| = I/2`, `‖a‖ = ‖b‖ = 1`), then
`q(C) ≥ 0` for every rank-`≤ 2` operator `C` on `ℂ^{κ → ι}`. -/
theorem qfun_nonneg_of_trace_nonneg (hH : 2 ≤ Fintype.card (κ → ι))
    (h : ∀ a b : (κ → ι) × Fin 2 → ℂ,
      (∀ r r', ∑ x, a (x, r) * star (a (x, r')) = if r = r' then (1 / 2 : ℂ) else 0) →
      vnormSq a = 1 → vnormSq b = 1 →
      0 ≤ ((objective4 κ ι (Fin 2) * moment ![a, a, a, b]).trace).re)
    (C : Matrix (κ → ι) (κ → ι) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  refine qfun_nonneg_of_normalized (fun C' hC' hn => ?_) C hC
  obtain ⟨a, b, h1, h2, h3, h4⟩ := lift_exists C' hC' hH hn
  have hCab : C' = liftC a b := liftC_eq_of h1
  have ha : nsqC a = 1 := by
    rw [← ofReal_vnormSq, h3, Complex.ofReal_one]
  have hq := qfun_eq_trace_four a b ha
  have hpos := h a b h2 h3 h4
  rw [← hq, Complex.ofReal_re] at hpos
  rw [hCab]
  exact hpos

end WernerEndpoint

end

#print axioms WernerEndpoint.moment_eq_Y31
#print axioms WernerEndpoint.moment_eq_Y22
#print axioms WernerEndpoint.moment_eq_Y13
#print axioms WernerEndpoint.rank_smul_le'
#print axioms WernerEndpoint.qfun_nonneg_of_normalized
#print axioms WernerEndpoint.qfun_nonneg_of_trace_nonneg
