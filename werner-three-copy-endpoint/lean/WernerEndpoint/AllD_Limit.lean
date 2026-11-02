import WernerEndpoint.AllD_Coupled
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# All-d lemma chain, step 6 (item 6): the limit `t → 0`

* `posSemidef_of_tendsto`: the PSD cone is closed — a limit of eventually PSD real matrices is PSD.
* `SiteCert tab N` (the verifier's (A2)–(A4) for one module, as a statement at every `d ≥ 4`): the
  `t`-polynomial matrices `N(p) ∈ ℝ[t]^{k×k}` satisfy, at every `d ≥ 4`,
  `∑_{p'} G_d(p, p') N(p')(1/d) = c · F(p)` for some `c > 0` and some module `F` of the table
  (`ModuleAt d tab F`). With `c = den(1/d) d^{α+4}` and `F = F_r(·)(d)` this is (A4), and
  `ModuleAt` follows from (A2)–(A3) by `moduleAt_of_verifier`.
* `continuous_blockOp_eval`: the full block operator built from `N(t)` is continuous in `t`.
* **`blockOp_word_t0_posSemidef`**, **`blockOp_coupled_T3_t0_posSemidef`**,
  **`blockOp_coupled_T23_t0_posSemidef`**: for **every** local dimension `e` (including
  `e = 0, …, 3`) and every trace-coordinate vector `μ` of every `a, b` at dimension `e`, the full
  word / coupled operator built from the `t = 0` matrices `N(p)(0)` is PSD. Proof: pad `a, b`
  into every `d ≥ max(e, 4)` (`isMCoord_embVec`: the same `μ`; item 1), apply the `t = 1/d`
  positivity of `AllD_Blocks` / `AllD_Coupled`, and pass to the limit `d → ∞`.
-/

open Matrix Filter Topology Polynomial
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

/-! ### Closedness of the PSD cone -/

theorem posSemidef_of_tendsto {n : Type*} [Fintype n] {f : ℕ → Matrix n n ℝ} {M : Matrix n n ℝ}
    (hf : Tendsto f atTop (𝓝 M)) (h : ∀ᶠ d in atTop, (f d).PosSemidef) : M.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : Tendsto (fun d => (f d)ᵀ) atTop (𝓝 Mᵀ) :=
      ((continuous_id.matrix_transpose).tendsto M).comp hf
    have h2 : Tendsto (fun d => (f d)ᵀ) atTop (𝓝 M) := by
      refine hf.congr' ?_
      filter_upwards [h] with d hd
      have := hd.1.eq
      rw [conjTranspose_eq_transpose_of_trivial] at this
      exact this.symm
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact tendsto_nhds_unique h1 h2
  · have hc : Continuous fun A : Matrix n n ℝ => star x ⬝ᵥ (A *ᵥ x) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact ge_of_tendsto ((hc.tendsto M).comp hf) (h.mono fun d hd => hd.2 x)

/-- If `L` is continuous at `0` and `L(1/d) ⪰ 0` for all large `d`, then `L(0) ⪰ 0`. -/
theorem posSemidef_at_zero {n : Type*} [Fintype n] {L : ℝ → Matrix n n ℝ}
    (hL : Continuous L) (d₀ : ℕ) (h : ∀ d : ℕ, d₀ ≤ d → (L (1 / (d : ℝ))).PosSemidef) :
    (L 0).PosSemidef :=
  posSemidef_of_tendsto ((hL.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat)
    (eventually_atTop.mpr ⟨d₀, h⟩)

/-! ### `t`-polynomial site data -/

/-- Evaluation of a polynomial matrix at `t`. -/
abbrev evalM {k : Type*} (t : ℝ) (A : Matrix k k ℝ[X]) : Matrix k k ℝ := A.map (Polynomial.eval t)

/-- **A `d`-uniform site module** (verifier (A2)–(A4)): at every `d ≥ 4` the `t`-polynomial
matrices evaluated at `t = 1/d` are, after the Weingarten matrix `G_d`, a positive multiple of a
module of the table `tab`. -/
def SiteCert {k : Type*} [Fintype k] (tab : P4 → P4 → P4 × ℕ) (N : P4 → Matrix k k ℝ[X]) :
    Prop :=
  ∀ d : ℕ, 4 ≤ d → ∃ (F : P4 → Matrix k k ℝ) (c : ℝ), 0 < c ∧ ModuleAt d tab F ∧
    ∀ p, ∑ p', gram d p p' • evalM (1 / (d : ℝ)) (N p') = c • F p

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem continuous_blockOp_eval {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]) (Fq : P4 → Matrix Kq Kq ℝ) (mp : P4 ≃ P4)
    (m : Tup κ → ℝ) :
    Continuous fun t : ℝ => blockOp (fun i p => evalM t (N i p)) Fq mp m := by
  unfold blockOp
  refine continuous_finset_sum _ fun s _ => Continuous.const_smul ?_ _
  refine continuous_matrix fun X Y => ?_
  simp only [rtens, Matrix.of_apply, Matrix.map_apply]
  exact (continuous_finset_prod _ fun i _ => Polynomial.continuous _).mul continuous_const

/-- Choice of the module data of a family of site certificates at one `d`. -/
theorem siteCert_at {K : κ → Type*} [∀ i, Fintype (K i)] {tab : P4 → P4 → P4 × ℕ}
    {N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]} (hN : ∀ i, SiteCert tab (N i)) {d : ℕ}
    (hd : 4 ≤ d) :
    ∃ (F : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (c : κ → ℝ), (∀ i, 0 < c i) ∧
      (∀ i, ModuleAt d tab (F i)) ∧
      ∀ i p, ∑ p', gram d p p' • evalM (1 / (d : ℝ)) (N i p') = c i • F i p := by
  choose F c hc hF hW using fun i => hN i d hd
  exact ⟨F, c, hc, hF, hW⟩

/-- Padding a trace-coordinate vector into `Fin d`, `e ≤ d`. -/
theorem isMCoord_pad {e d : ℕ} (hed : e ≤ d) {a b : (κ → Fin e) × Fin 2 → ℂ}
    {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    IsMCoord (embVec (Fin.castLEEmb hed) a) (embVec (Fin.castLEEmb hed) b) μ :=
  isMCoord_embVec _ hμ

/-- **Item 6, word blocks.** For every local dimension `e`, the `t = 0` word operator is PSD at
every trace-coordinate vector of dimension `e`. -/
theorem blockOp_word_t0_posSemidef {T : Finset (Fin 4)} (hT : IsCut T) {tab : P4 → P4 → P4 × ℕ}
    (htab : ∀ d : ℕ, 4 ≤ d → TabAt T d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]) (hN : ∀ i, SiteCert tab (N i))
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J)
    {e : ℕ} {a b : (κ → Fin e) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ)
    (f : Fam) :
    (blockOp (fun i p => evalM 0 (N i p)) Fq (Equiv.refl P4) (μ f)).PosSemidef := by
  refine posSemidef_at_zero (L := fun t => blockOp (fun i p => evalM t (N i p)) Fq
    (Equiv.refl P4) (μ f)) (continuous_blockOp_eval N Fq _ _) (max e 4) fun d hd => ?_
  have hd4 : 4 ≤ d := le_of_max_le_right hd
  obtain ⟨F, c, hc, hF, hW⟩ := siteCert_at hN hd4
  exact blockOp_word_posSemidef hd4 hT (htab d hd4) F _ hF c hc hW hJ
    (isMCoord_pad (le_of_max_le_left hd) hμ) f

theorem continuous_coupled_eval {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]) (Fq : P4 → Matrix Kq Kq ℝ)
    (mp₁ mp₂ mp₃ : P4 ≃ P4) (μ : Fam → Tup κ → ℝ) :
    Continuous fun t : ℝ =>
      fromBlocks (blockOp (fun i p => evalM t (N i p)) Fq mp₁ (μ .f31))
        (blockOp (fun i p => evalM t (N i p)) Fq mp₂ (μ .f22))
        (blockOp (fun i p => evalM t (N i p)) Fq mp₂ (μ .f22))ᵀ
        (blockOp (fun i p => evalM t (N i p)) Fq mp₃ (μ .f13)) :=
  Continuous.matrix_fromBlocks (continuous_blockOp_eval N Fq _ _)
    (continuous_blockOp_eval N Fq _ _) (continuous_blockOp_eval N Fq _ _).matrix_transpose
    (continuous_blockOp_eval N Fq _ _)

/-- **Item 6, coupled block `T = {3}`.** -/
theorem blockOp_coupled_T3_t0_posSemidef {tab : P4 → P4 → P4 × ℕ}
    (htab : ∀ d : ℕ, 4 ≤ d → TabAt {3} d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]) (hN : ∀ i, SiteCert tab (N i))
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt {3} Fq J)
    {e : ℕ} {a b : (κ → Fin e) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    (fromBlocks (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT3_31 mT3_31_surj) (μ .f31))
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT3_22 mT3_22_surj) (μ .f22))
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT3_22 mT3_22_surj) (μ .f22))ᵀ
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT3_13 mT3_13_surj) (μ .f13))).PosSemidef := by
  refine posSemidef_at_zero (continuous_coupled_eval N Fq _ _ _ μ) (max e 4) fun d hd => ?_
  have hd4 : 4 ≤ d := le_of_max_le_right hd
  obtain ⟨F, c, hc, hF, hW⟩ := siteCert_at hN hd4
  exact blockOp_coupled_T3_posSemidef hd4 (htab d hd4) F _ hF c hc hW hJ
    (isMCoord_pad (le_of_max_le_left hd) hμ)

/-- **Item 6, coupled block `T = {2,3}`.** -/
theorem blockOp_coupled_T23_t0_posSemidef {tab : P4 → P4 → P4 × ℕ}
    (htab : ∀ d : ℕ, 4 ≤ d → TabAt {2, 3} d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ[X]) (hN : ∀ i, SiteCert tab (N i))
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt {2, 3} Fq J)
    {e : ℕ} {a b : (κ → Fin e) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    (fromBlocks (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT23_31 mT23_31_surj) (μ .f31))
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT23_22 mT23_22_surj) (μ .f22))
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT23_22 mT23_22_surj) (μ .f22))ᵀ
      (blockOp (fun i p => evalM 0 (N i p)) Fq (mpE mT23_13 mT23_13_surj) (μ .f13))).PosSemidef := by
  refine posSemidef_at_zero (continuous_coupled_eval N Fq _ _ _ μ) (max e 4) fun d hd => ?_
  have hd4 : 4 ≤ d := le_of_max_le_right hd
  obtain ⟨F, c, hc, hF, hW⟩ := siteCert_at hN hd4
  exact blockOp_coupled_T23_posSemidef hd4 (htab d hd4) F _ hF c hc hW hJ
    (isMCoord_pad (le_of_max_le_left hd) hμ)

end WernerEndpoint

end

#print axioms WernerEndpoint.posSemidef_of_tendsto
#print axioms WernerEndpoint.posSemidef_at_zero
#print axioms WernerEndpoint.continuous_blockOp_eval
#print axioms WernerEndpoint.blockOp_word_t0_posSemidef
#print axioms WernerEndpoint.blockOp_coupled_T3_t0_posSemidef
#print axioms WernerEndpoint.blockOp_coupled_T23_t0_posSemidef
