import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Order

/-!
# L9: pairing and margin (layer A of `exact_certificate_d5/LEAN_PLAN.md`)

* (i)  `⟨X, M⟩ ≥ 0` for positive semidefinite `X`, `M`
  (`trace_mul_nonneg`, `pairing_nonneg`, `pairing_nonneg_real`).
* (ii) If `A - μ I` is PSD (resp. PD) and `D` is a real diagonal with `|D_ii| ≤ μ`, then `A + D`
  is PSD (resp. PD) (`posSemidef_add_diagonal_of_margin`, `posDef_add_diagonal_of_margin`,
  real versions `..._real`).
* The certificate form used by `verify_d5.py` (D):
  `X = X0 / 2^s + diag(Δ) / DEN` with `X0 / 2^s - μ I ≻ 0` and `|Δ_i| / DEN ≤ μ` gives `X ≻ 0`
  (`certificate_posDef`), hence `⟨X, M⟩ ≥ 0` for every PSD `M` (`certificate_pairing_nonneg`).
  `Δ` is a function of the index, so each diagonal entry is corrected once
  (the verifier's "distinct Δ indices" check is what makes the data a function).
-/

open Matrix
open scoped ComplexOrder

namespace WernerEndpoint

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

open scoped MatrixOrder in
/-- **L9 (i).** For positive semidefinite `X` and `M`, `0 ≤ tr (X * M)` (in the `ComplexOrder`
sense over `ℂ`: the trace is real and nonnegative). -/
theorem trace_mul_nonneg {X M : Matrix n n 𝕜} (hX : X.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (X * M).trace := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [hB, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm]
  exact (hM.mul_mul_conjTranspose_same B).trace_nonneg

/-- **L9 (i), real part.** -/
theorem re_trace_mul_nonneg {X M : Matrix n n 𝕜} (hX : X.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ RCLike.re (X * M).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg hX hM)).1

/-- **L9 (i), Hilbert–Schmidt form.** `⟨X, M⟩ = ∑ᵢⱼ conj(X i j) * M i j ≥ 0` for PSD `X`, `M`. -/
theorem pairing_nonneg {X M : Matrix n n 𝕜} (hX : X.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ ∑ i, ∑ j, star (X i j) * M i j := by
  have e : ∑ i, ∑ j, star (X i j) * M i j = (X * M).trace := by
    simp only [hX.isHermitian.apply]
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [e]
  exact trace_mul_nonneg hX hM

/-- The diagonal shift identity behind the margin argument. -/
theorem add_diagonal_split [DecidableEq n] (A : Matrix n n 𝕜) (μ : ℝ) (d : n → ℝ) :
    A + diagonal (fun i => (d i : 𝕜)) =
      (A - (μ : 𝕜) • (1 : Matrix n n 𝕜)) + diagonal (fun i => ((μ + d i : ℝ) : 𝕜)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul,
      mul_one, RCLike.ofReal_add]
    ring
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, smul_zero,
      sub_zero, add_zero]

/-- **L9 (ii), PSD form.** If `A - μ I ⪰ 0` and `D = diag(d)` is real with `|d i| ≤ μ`,
then `A + D ⪰ 0`. -/
theorem posSemidef_add_diagonal_of_margin [DecidableEq n] {A : Matrix n n 𝕜} {μ : ℝ}
    {d : n → ℝ} (hA : (A - (μ : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef) (hd : ∀ i, |d i| ≤ μ) :
    (A + diagonal fun i => (d i : 𝕜)).PosSemidef := by
  rw [add_diagonal_split A μ d]
  refine hA.add (posSemidef_diagonal_iff.mpr fun i => ?_)
  show 0 ≤ ((μ + d i : ℝ) : 𝕜)
  exact RCLike.ofReal_nonneg.mpr (by linarith [(abs_le.mp (hd i)).1])

/-- **L9 (ii), PD form.** If `A - μ I ≻ 0` and `D = diag(d)` is real with `|d i| ≤ μ`,
then `A + D ≻ 0`. -/
theorem posDef_add_diagonal_of_margin [DecidableEq n] {A : Matrix n n 𝕜} {μ : ℝ}
    {d : n → ℝ} (hA : (A - (μ : 𝕜) • (1 : Matrix n n 𝕜)).PosDef) (hd : ∀ i, |d i| ≤ μ) :
    (A + diagonal fun i => (d i : 𝕜)).PosDef := by
  rw [add_diagonal_split A μ d]
  refine hA.add_posSemidef (posSemidef_diagonal_iff.mpr fun i => ?_)
  show 0 ≤ ((μ + d i : ℝ) : 𝕜)
  exact RCLike.ofReal_nonneg.mpr (by linarith [(abs_le.mp (hd i)).1])

end RCLike

section Real

variable {n : Type*} [Fintype n]

/-- **L9 (i), real symmetric form** (the pairing `∑ᵢⱼ X_ij M_ij` computed by the verifier). -/
theorem pairing_nonneg_real {X M : Matrix n n ℝ} (hX : X.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ ∑ i, ∑ j, X i j * M i j := by
  have e : (X * M).trace = ∑ i, ∑ j, X i j * M i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hM.isHermitian.apply i j, star_trivial]
  exact (trace_mul_nonneg hX hM).trans_eq e

/-- **L9 (ii), real PD form.** -/
theorem posDef_add_diagonal_of_margin_real [DecidableEq n] {A : Matrix n n ℝ} {μ : ℝ}
    {d : n → ℝ} (hA : (A - μ • (1 : Matrix n n ℝ)).PosDef) (hd : ∀ i, |d i| ≤ μ) :
    (A + diagonal d).PosDef := by
  have hsplit : A + diagonal d = (A - μ • (1 : Matrix n n ℝ)) + diagonal (fun i => μ + d i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul,
        mul_one]
      ring
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h,
        smul_zero, sub_zero, add_zero]
  rw [hsplit]
  refine hA.add_posSemidef (posSemidef_diagonal_iff.mpr fun i => ?_)
  show 0 ≤ μ + d i
  linarith [(abs_le.mp (hd i)).1]

/-- **L9 (ii), real PSD form.** -/
theorem posSemidef_add_diagonal_of_margin_real [DecidableEq n] {A : Matrix n n ℝ} {μ : ℝ}
    {d : n → ℝ} (hA : (A - μ • (1 : Matrix n n ℝ)).PosSemidef) (hd : ∀ i, |d i| ≤ μ) :
    (A + diagonal d).PosSemidef := by
  have hsplit : A + diagonal d = (A - μ • (1 : Matrix n n ℝ)) + diagonal (fun i => μ + d i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul,
        mul_one]
      ring
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h,
        smul_zero, sub_zero, add_zero]
  rw [hsplit]
  refine hA.add (posSemidef_diagonal_iff.mpr fun i => ?_)
  show 0 ≤ μ + d i
  linarith [(abs_le.mp (hd i)).1]

/-- **L9, certificate form** (`verify_d5.py` step (D)). With an integer matrix `X0`, a scale
exponent `s : ℤ`, a denominator `DEN`, integer corrections `Δ`, and a margin `μ`:
if `X0 / 2^s - μ I ≻ 0` and `|Δ i| / DEN ≤ μ` for every `i`, then
`X = X0 / 2^s + diag(Δ) / DEN ≻ 0`. -/
theorem certificate_posDef [DecidableEq n] (X0 : Matrix n n ℤ) (s : ℤ) (DEN : ℕ) (Δ : n → ℤ)
    (μ : ℝ)
    (hPD : (((2 : ℝ) ^ s)⁻¹ • X0.map (Int.cast : ℤ → ℝ) - μ • (1 : Matrix n n ℝ)).PosDef)
    (hΔ : ∀ i, |(Δ i : ℝ)| / DEN ≤ μ) :
    (((2 : ℝ) ^ s)⁻¹ • X0.map (Int.cast : ℤ → ℝ) +
      diagonal fun i => (Δ i : ℝ) / DEN).PosDef :=
  posDef_add_diagonal_of_margin_real hPD fun i => by
    show |(Δ i : ℝ) / DEN| ≤ μ
    rw [abs_div, Nat.abs_cast]
    exact hΔ i

/-- **L9, certificate pairing.** Under the hypotheses of `certificate_posDef`, the pairing of the
certificate matrix `X` with any PSD block value `M` is nonnegative. -/
theorem certificate_pairing_nonneg [DecidableEq n] (X0 : Matrix n n ℤ) (s : ℤ) (DEN : ℕ)
    (Δ : n → ℤ) (μ : ℝ)
    (hPD : (((2 : ℝ) ^ s)⁻¹ • X0.map (Int.cast : ℤ → ℝ) - μ • (1 : Matrix n n ℝ)).PosDef)
    (hΔ : ∀ i, |(Δ i : ℝ)| / DEN ≤ μ) {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    0 ≤ ∑ i, ∑ j, (((2 : ℝ) ^ s)⁻¹ • X0.map (Int.cast : ℤ → ℝ) +
      diagonal fun i => (Δ i : ℝ) / DEN) i j * M i j :=
  pairing_nonneg_real (certificate_posDef X0 s DEN Δ μ hPD hΔ).posSemidef hM

end Real

end WernerEndpoint

#print axioms WernerEndpoint.trace_mul_nonneg
#print axioms WernerEndpoint.re_trace_mul_nonneg
#print axioms WernerEndpoint.pairing_nonneg
#print axioms WernerEndpoint.posSemidef_add_diagonal_of_margin
#print axioms WernerEndpoint.posDef_add_diagonal_of_margin
#print axioms WernerEndpoint.pairing_nonneg_real
#print axioms WernerEndpoint.posDef_add_diagonal_of_margin_real
#print axioms WernerEndpoint.posSemidef_add_diagonal_of_margin_real
#print axioms WernerEndpoint.certificate_posDef
#print axioms WernerEndpoint.certificate_pairing_nonneg
