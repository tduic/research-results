import WernerEndpoint.LayerC_BrauerCore
import WernerEndpoint.L4_WordPositivity
import WernerEndpoint.L5_CoupledGram

/-!
# Layer C: partial transpose and literal rearrangement of Brauer operators

* `ptrans_br`: `Γ_T (br μ) = br (τ_T ∘ μ ∘ τ_T)`; `rearr_br`: `rearr σ (br μ) = br (σ ∘ μ ∘ σ⁻¹)`.
  So a diagram identity `rearr σ (P_p) = Γ_T (P_{p'})` follows from an identity of slot maps,
  for **every** local dimension.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace WernerEndpoint

section Brauer

variable {R α : Type*} [Fintype R] [DecidableEq R] [Fintype α] [DecidableEq α]

theorem elim_ptrans (T : Finset R) (x y : R → α) :
    Sum.elim (fun r => if r ∈ T then y r else x r) (fun r => if r ∈ T then x r else y r) =
      Sum.elim x y ∘ tauT T := by
  funext q
  cases q with
  | inl j => by_cases h : j ∈ T <;> simp [tauT, h]
  | inr j => by_cases h : j ∈ T <;> simp [tauT, h]

/-- `Γ_T (br μ) = br (τ_T ∘ μ ∘ τ_T)`. -/
theorem ptrans_br (T : Finset R) (μ : R ⊕ R → R ⊕ R) :
    ptrans (ι := fun _ : R => α) T (br α μ) = br α (fun q => tauT T (μ (tauT T q))) := by
  ext x y
  simp only [ptrans, br, Matrix.of_apply]
  rw [elim_ptrans]
  refine if_congr ⟨fun h q => ?_, fun h q => ?_⟩ rfl rfl
  · have := h (tauT T q)
    simpa only [Function.comp_apply, tauT_tauT] using this
  · have := h (tauT T q)
    simpa only [Function.comp_apply, tauT_tauT] using this

theorem elim_rearr (σ : R ⊕ R ≃ R ⊕ R) (x y : R → α) :
    Sum.elim (fun s => Sum.elim x y (σ (.inl s))) (fun s => Sum.elim x y (σ (.inr s))) =
      Sum.elim x y ∘ σ := by
  funext q
  cases q <;> rfl

/-- `rearr σ (br μ) = br (σ ∘ μ ∘ σ⁻¹)`. -/
theorem rearr_br (σ : R ⊕ R ≃ R ⊕ R) (μ : R ⊕ R → R ⊕ R) :
    rearr σ (br α μ) = br α (fun q => σ (μ (σ.symm q))) := by
  ext x y
  simp only [rearr, br, Matrix.of_apply]
  rw [elim_rearr]
  refine if_congr ⟨fun h q => ?_, fun h q => ?_⟩ rfl rfl
  · have := h (σ.symm q)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
  · have := h (σ q)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this

end Brauer

end WernerEndpoint

#print axioms WernerEndpoint.ptrans_br
#print axioms WernerEndpoint.rearr_br
