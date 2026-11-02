import WernerEndpoint.AllD_Limit

/-!
# From the verifier's polynomial identities to `SiteCert`

`verify_t0.py` (A2) checks, as identities of integer-polynomial matrices in `d`,
`F(p)ᵀ = F(p⁻¹)` and `F(p) · adj F(e) · F(q) = d^{l(p,q)} det F(e) · F(s(p,q))`; (A3) checks
`F(e)(d) ≻ 0` for every real `d ≥ 4`; (A4) checks the Weingarten relation
`∑_{p'} d^{cyc(p⁻¹p')} N(p')(1/d) = den(1/d) d^{α+4} F(p)(d)`.

`siteCert_of_poly`: these three facts (the first two as polynomial identities, the last two at
every integer `d ≥ 4`, with any positive scalar in place of `den(1/d) d^{α+4}`) give
`SiteCert tab N`. Evaluation at `d` is a ring homomorphism, so it commutes with products,
adjugates and determinants.
-/

open Matrix Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

theorem siteCert_of_poly {k : Type*} [Fintype k] [DecidableEq k] {tab : P4 → P4 → P4 × ℕ}
    (F N : P4 → Matrix k k ℝ[X])
    (hT : ∀ p, (F p)ᵀ = F p⁻¹)
    (hhom : ∀ p q, F p * (F 1).adjugate * F q = (X ^ (tab p q).2 * (F 1).det) • F (tab p q).1)
    (hpd : ∀ d : ℕ, 4 ≤ d → (evalM (d : ℝ) (F 1)).PosDef)
    (c : ℕ → ℝ) (hc : ∀ d : ℕ, 4 ≤ d → 0 < c d)
    (hW : ∀ d : ℕ, 4 ≤ d → ∀ p,
      ∑ p', gram d p p' • evalM (1 / (d : ℝ)) (N p') = c d • evalM (d : ℝ) (F p)) :
    SiteCert tab N := by
  intro d hd
  refine ⟨fun p => evalM (d : ℝ) (F p), c d, hc d hd, moduleAt_of_verifier ?_ ?_ (hpd d hd),
    hW d hd⟩
  · intro p
    rw [← hT p]
    ext i j
    rfl
  · intro p q
    set φ := Polynomial.evalRingHom (d : ℝ)
    have hm : ∀ A : Matrix k k ℝ[X], evalM (d : ℝ) A = φ.mapMatrix A := fun A => rfl
    have h := congrArg φ.mapMatrix (hhom p q)
    rw [map_mul, map_mul, RingHom.map_adjugate] at h
    simp only [hm]
    rw [h]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      map_pow]
    rw [RingHom.map_det]
    simp [φ]

end WernerEndpoint

end

#print axioms WernerEndpoint.siteCert_of_poly
