import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Block
import WernerEndpoint.L9_Pairing

/-!
# Layer C (L7, abstract part): the Hilbert–Schmidt projection onto a unital *-subalgebra

Route (Haar-free). For a subspace `𝒜` of `Matrix n n ℂ`, `IsHSProj 𝒜 Y Z` says that `Z` is the
Hilbert–Schmidt orthogonal projection of `Y` onto `𝒜`: `Z ∈ 𝒜` and `⟨A, Y - Z⟩_HS = 0` for every
`A ∈ 𝒜` (`hs A B = ∑ᵢⱼ conj(A i j) B i j = Tr(Aᴴ B)`).

* `exists_isHSProj`, `IsHSProj.unique`: the projection exists (for `*`-closed `𝒜`; a dimension
  count on `𝒜 → Dual 𝒜`) and is unique.
* `IsHSProj.trace_mul`: `Tr[A Z] = Tr[A Y]` for `A ∈ 𝒜` (self-adjointness of the projection).
* `IsHSProj.conjTranspose`, `IsHSProj.isHermitian`: the projection commutes with `ᴴ`.
* `IsHSProj.mul_left`, `IsHSProj.mul_right`: **bimodule** property for `B ∈ 𝒜` (`IsStarAlg 𝒜`).
* `IsHSProj.add`, `IsHSProj.smul`, `IsHSProj.sum`: linearity.
* `IsHSProj.posSemidef`: **positivity**. If `𝒜` is a unital `*`-subalgebra and `Y ⪰ 0`, then
  `Z ⪰ 0`. Proof: `Z` is Hermitian; if an eigenvalue `λ₀ < 0`, the real polynomial
  `p = ∏_{λ ≥ 0} (X - λ)` gives `B = p(Z) ∈ 𝒜` and `A = BᴴB ∈ 𝒜`, `A ⪰ 0`; then
  `0 ≤ Tr[A Y] = Tr[A Z] = ∑ᵢ p(λᵢ)² λᵢ < 0` (eigenbasis of `Z`, via Mathlib's Hermitian
  functional calculus `cfc_polynomial` / `IsHermitian.cfc_eq`).
* `blockAlg`, `isStarAlg_blockAlg`, `isHSProj_fromBlocks`, `posSemidef_fromBlocks_of_isHSProj`:
  **2-positivity**. The 2×2 block matrices over `𝒜` form a unital `*`-subalgebra of
  `Matrix (n ⊕ n) (n ⊕ n) ℂ`, and its projection acts blockwise; positivity there is
  2-positivity of the projection, which the coupled blocks need.
* `IsHSProj.map`: transport along a map that preserves orthogonality and carries `𝒜` onto `𝒜'`
  (index rearrangements, partial transposes, entrywise conjugation); `hs_reindex`,
  `hs_map_star` are the two cases used.
-/

open Matrix Polynomial
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section HS

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hilbert–Schmidt inner product `⟨A, B⟩ = ∑ᵢⱼ conj (A i j) * B i j`. -/
def hs (A B : Matrix n n ℂ) : ℂ := ∑ i, ∑ j, star (A i j) * B i j

theorem hs_eq_trace (A B : Matrix n n ℂ) : hs A B = (Aᴴ * B).trace := by
  simp only [hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem hs_sub_right (A B C : Matrix n n ℂ) : hs A (B - C) = hs A B - hs A C := by
  simp only [hs, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hs_add_right (A B C : Matrix n n ℂ) : hs A (B + C) = hs A B + hs A C := by
  simp only [hs, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hs_smul_right (A B : Matrix n n ℂ) (c : ℂ) : hs A (c • B) = c * hs A B := by
  simp only [hs, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hs_self_eq_zero {A : Matrix n n ℂ} : hs A A = 0 ↔ A = 0 := by
  rw [hs_eq_trace]
  exact trace_conjTranspose_mul_self_eq_zero_iff

/-- `⟨A, Mᴴ⟩ = conj ⟨Aᴴ, M⟩`. -/
theorem hs_conjTranspose (A M : Matrix n n ℂ) : hs A Mᴴ = star (hs Aᴴ M) := by
  simp only [hs, Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]

/-- A unital `*`-subalgebra (as a complex subspace). -/
structure IsStarAlg (𝒜 : Submodule ℂ (Matrix n n ℂ)) : Prop where
  one_mem : (1 : Matrix n n ℂ) ∈ 𝒜
  mul_mem : ∀ {A B : Matrix n n ℂ}, A ∈ 𝒜 → B ∈ 𝒜 → A * B ∈ 𝒜
  star_mem : ∀ {A : Matrix n n ℂ}, A ∈ 𝒜 → Aᴴ ∈ 𝒜

/-- `Z` is the Hilbert–Schmidt orthogonal projection of `Y` onto `𝒜`. -/
def IsHSProj (𝒜 : Submodule ℂ (Matrix n n ℂ)) (Y Z : Matrix n n ℂ) : Prop :=
  Z ∈ 𝒜 ∧ ∀ A ∈ 𝒜, hs A (Y - Z) = 0

variable {𝒜 : Submodule ℂ (Matrix n n ℂ)}

theorem IsHSProj.unique {Y Z Z' : Matrix n n ℂ} (h1 : IsHSProj 𝒜 Y Z) (h2 : IsHSProj 𝒜 Y Z') :
    Z = Z' := by
  have hm : Z - Z' ∈ 𝒜 := 𝒜.sub_mem h1.1 h2.1
  have h0 : hs (Z - Z') (Z - Z') = 0 := by
    have e : Z - Z' = (Y - Z') - (Y - Z) := by abel
    calc hs (Z - Z') (Z - Z') = hs (Z - Z') ((Y - Z') - (Y - Z)) := by rw [← e]
      _ = 0 := by rw [hs_sub_right, h2.2 _ hm, h1.2 _ hm, sub_zero]
  exact sub_eq_zero.mp (hs_self_eq_zero.mp h0)

/-- `Tr[A Z] = Tr[A Y]` for `A` in a `*`-closed `𝒜`. -/
theorem IsHSProj.trace_mul (hstar : ∀ {A : Matrix n n ℂ}, A ∈ 𝒜 → Aᴴ ∈ 𝒜) {Y Z : Matrix n n ℂ}
    (h : IsHSProj 𝒜 Y Z) {A : Matrix n n ℂ} (hA : A ∈ 𝒜) : (A * Z).trace = (A * Y).trace := by
  have := h.2 _ (hstar hA)
  rw [hs_eq_trace, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.trace_sub,
    sub_eq_zero] at this
  exact this.symm

/-- **Existence** of the projection onto a `*`-closed subspace. -/
theorem exists_isHSProj (hstar : ∀ {A : Matrix n n ℂ}, A ∈ 𝒜 → Aᴴ ∈ 𝒜) (Y : Matrix n n ℂ) :
    ∃ Z, IsHSProj 𝒜 Y Z := by
  let Φ : 𝒜 →ₗ[ℂ] Module.Dual ℂ 𝒜 :=
    LinearMap.mk₂ ℂ (fun Z A => ((A : Matrix n n ℂ) * (Z : Matrix n n ℂ)).trace)
      (fun Z₁ Z₂ A => by simp [Matrix.mul_add, Matrix.trace_add])
      (fun c Z A => by simp [Matrix.mul_smul, Matrix.trace_smul])
      (fun Z A₁ A₂ => by simp [Matrix.add_mul, Matrix.trace_add])
      (fun c Z A => by simp [Matrix.smul_mul, Matrix.trace_smul])
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Z hZ
    have h0 := LinearMap.congr_fun hZ ⟨(Z : Matrix n n ℂ)ᴴ, hstar Z.2⟩
    simp only [Φ, LinearMap.mk₂_apply, LinearMap.zero_apply] at h0
    exact Subtype.ext (trace_conjTranspose_mul_self_eq_zero_iff.mp h0)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp hinj
  let ψ : Module.Dual ℂ 𝒜 :=
    (Matrix.traceLinearMap n ℂ ℂ).comp ((LinearMap.mulRight ℂ Y).comp 𝒜.subtype)
  obtain ⟨Z, hZ⟩ := hsurj ψ
  refine ⟨Z, Z.2, fun A hA => ?_⟩
  have h1 := LinearMap.congr_fun hZ ⟨Aᴴ, hstar hA⟩
  simp only [Φ, ψ, LinearMap.mk₂_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.mulRight_apply, Matrix.traceLinearMap_apply] at h1
  rw [hs_eq_trace, Matrix.mul_sub, Matrix.trace_sub, h1, sub_self]

theorem IsHSProj.conjTranspose (hstar : ∀ {A : Matrix n n ℂ}, A ∈ 𝒜 → Aᴴ ∈ 𝒜)
    {Y Z : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z) : IsHSProj 𝒜 Yᴴ Zᴴ := by
  refine ⟨hstar h.1, fun A hA => ?_⟩
  rw [← conjTranspose_sub, hs_conjTranspose, h.2 _ (hstar hA), star_zero]

theorem IsHSProj.isHermitian (hstar : ∀ {A : Matrix n n ℂ}, A ∈ 𝒜 → Aᴴ ∈ 𝒜)
    {Y Z : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z) (hY : Y.IsHermitian) : Z.IsHermitian := by
  have h' := h.conjTranspose hstar
  rw [hY.eq] at h'
  exact h'.unique h

theorem IsHSProj.add {Y₁ Y₂ Z₁ Z₂ : Matrix n n ℂ} (h₁ : IsHSProj 𝒜 Y₁ Z₁)
    (h₂ : IsHSProj 𝒜 Y₂ Z₂) : IsHSProj 𝒜 (Y₁ + Y₂) (Z₁ + Z₂) := by
  refine ⟨𝒜.add_mem h₁.1 h₂.1, fun A hA => ?_⟩
  have e : Y₁ + Y₂ - (Z₁ + Z₂) = (Y₁ - Z₁) + (Y₂ - Z₂) := by abel
  rw [e, hs_add_right, h₁.2 A hA, h₂.2 A hA, add_zero]

theorem IsHSProj.smul {Y Z : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z) (c : ℂ) :
    IsHSProj 𝒜 (c • Y) (c • Z) := by
  refine ⟨𝒜.smul_mem c h.1, fun A hA => ?_⟩
  rw [← smul_sub, hs_smul_right, h.2 A hA, mul_zero]

theorem isHSProj_zero : IsHSProj 𝒜 0 0 := ⟨𝒜.zero_mem, fun A _ => by simp [hs]⟩

theorem IsHSProj.sum {ι : Type*} (s : Finset ι) {Y Z : ι → Matrix n n ℂ}
    (h : ∀ i ∈ s, IsHSProj 𝒜 (Y i) (Z i)) : IsHSProj 𝒜 (∑ i ∈ s, Y i) (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isHSProj_zero (𝒜 := 𝒜))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Bimodule property** (left). -/
theorem IsHSProj.mul_left (h𝒜 : IsStarAlg 𝒜) {Y Z B : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z)
    (hB : B ∈ 𝒜) : IsHSProj 𝒜 (B * Y) (B * Z) := by
  refine ⟨h𝒜.mul_mem hB h.1, fun A hA => ?_⟩
  have := h.2 _ (h𝒜.mul_mem (h𝒜.star_mem hB) hA)
  rw [hs_eq_trace] at this ⊢
  rw [conjTranspose_mul, conjTranspose_conjTranspose] at this
  rw [← Matrix.mul_sub, ← Matrix.mul_assoc]
  exact this

/-- **Bimodule property** (right). -/
theorem IsHSProj.mul_right (h𝒜 : IsStarAlg 𝒜) {Y Z B : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z)
    (hB : B ∈ 𝒜) : IsHSProj 𝒜 (Y * B) (Z * B) := by
  refine ⟨h𝒜.mul_mem h.1 hB, fun A hA => ?_⟩
  have := h.2 _ (h𝒜.mul_mem hA (h𝒜.star_mem hB))
  rw [hs_eq_trace] at this ⊢
  rw [conjTranspose_mul, conjTranspose_conjTranspose] at this
  rw [← Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact this

/-- Real polynomials in an element of a unital subalgebra stay in it. -/
theorem aeval_mem (h𝒜 : IsStarAlg 𝒜) {Z : Matrix n n ℂ} (hZ : Z ∈ 𝒜) (p : ℝ[X]) :
    aeval Z p ∈ 𝒜 := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_of_tower_mem _ a h𝒜.one_mem
  | add p q hp hq => rw [map_add]; exact 𝒜.add_mem hp hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact h𝒜.mul_mem ih hZ

theorem conj_unitary_mul {U D₁ D₂ : Matrix n n ℂ} (hU : star U * U = 1) :
    (U * D₁ * star U) * (U * D₂ * star U) = U * (D₁ * D₂) * star U := by
  calc (U * D₁ * star U) * (U * D₂ * star U) = U * D₁ * (star U * U) * D₂ * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (D₁ * D₂) * star U := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem trace_conj_unitary {U D : Matrix n n ℂ} (hU : star U * U = 1) :
    (U * D * star U).trace = D.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem conjTranspose_conj_unitary (U D : Matrix n n ℂ) :
    (U * D * star U)ᴴ = U * Dᴴ * star U := by
  rw [conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star,
    star_eq_conjTranspose, Matrix.mul_assoc]

/-- **Positivity of the projection onto a unital `*`-subalgebra.** -/
theorem IsHSProj.posSemidef (h𝒜 : IsStarAlg 𝒜) {Y Z : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z)
    (hY : Y.PosSemidef) : Z.PosSemidef := by
  have hZ : Z.IsHermitian := h.isHermitian h𝒜.star_mem hY.isHermitian
  rw [hZ.posSemidef_iff_eigenvalues_nonneg]
  by_contra hneg
  rw [Pi.le_def] at hneg
  push_neg at hneg
  obtain ⟨i₀, hi₀⟩ := hneg
  replace hi₀ : hZ.eigenvalues i₀ < 0 := hi₀
  set ev := hZ.eigenvalues with hev
  set U : Matrix n n ℂ := (hZ.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : star U * U = 1 := unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.2
  let p : ℝ[X] := ∏ j ∈ Finset.univ.filter (fun j => 0 ≤ ev j), (X - C (ev j))
  set B : Matrix n n ℂ := aeval Z p with hBdef
  have hBmem : B ∈ 𝒜 := aeval_mem h𝒜 h.1 p
  have hsa : IsSelfAdjoint Z := hZ
  let dp : n → ℂ := fun i => ((p.eval (ev i) : ℝ) : ℂ)
  have hBeq : B = U * diagonal dp * star U := by
    rw [hBdef, ← cfc_polynomial p Z hsa, hZ.cfc_eq]
    rfl
  have hZeq : Z = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hZ.spectral_theorem]
    rfl
  set A := Bᴴ * B with hAdef
  have hAmem : A ∈ 𝒜 := h𝒜.mul_mem (h𝒜.star_mem hBmem) hBmem
  have hApsd : A.PosSemidef := posSemidef_conjTranspose_mul_self B
  have h1 : (A * Z).trace = (A * Y).trace := h.trace_mul h𝒜.star_mem hAmem
  have h2 : 0 ≤ (A * Y).trace := trace_mul_nonneg hApsd hY
  have hdpstar : (diagonal dp)ᴴ = diagonal dp := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [dp]
  have h3 : A * Z = U * diagonal (fun i => dp i * dp i * ((ev i : ℝ) : ℂ)) * star U := by
    rw [hAdef, hBeq, hZeq, conjTranspose_conj_unitary, hdpstar, conj_unitary_mul hU,
      conj_unitary_mul hU, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have h4 : (A * Z).trace =
      ((∑ i, (p.eval (ev i)) ^ 2 * ev i : ℝ) : ℂ) := by
    rw [h3, trace_conj_unitary hU, trace_diagonal]
    push_cast
    simp only [dp, sq]
  have hneg' : ∑ i, (p.eval (ev i)) ^ 2 * ev i < 0 := by
    have hterm : ∀ i, (p.eval (ev i)) ^ 2 * ev i ≤ 0 := by
      intro i
      by_cases hi : 0 ≤ ev i
      · have : p.eval (ev i) = 0 := by
          simp only [p, eval_prod, eval_sub, eval_X, eval_C]
          exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (sub_self _)
        rw [this]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_lt (not_le.mp hi))
    have hp0 : p.eval (ev i₀) ≠ 0 := by
      simp only [p, eval_prod, eval_sub, eval_X, eval_C]
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      have := (Finset.mem_filter.mp hj).2
      intro he
      have : ev i₀ = ev j := sub_eq_zero.mp he
      linarith
    have hlt : (p.eval (ev i₀)) ^ 2 * ev i₀ < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hp0) hi₀
    calc ∑ i, (p.eval (ev i)) ^ 2 * ev i < ∑ _i : n, (0 : ℝ) :=
          Finset.sum_lt_sum (fun i _ => hterm i) ⟨i₀, Finset.mem_univ _, hlt⟩
      _ = 0 := by simp
  rw [← h1, h4] at h2
  exact absurd (Complex.zero_le_real.mp h2) (not_le.mpr hneg')

/-! ### 2-positivity: the block algebra -/

/-- The 2×2 block matrices with all four blocks in `𝒜`. -/
def blockAlg (𝒜 : Submodule ℂ (Matrix n n ℂ)) : Submodule ℂ (Matrix (n ⊕ n) (n ⊕ n) ℂ) where
  carrier := {M | M.toBlocks₁₁ ∈ 𝒜 ∧ M.toBlocks₁₂ ∈ 𝒜 ∧ M.toBlocks₂₁ ∈ 𝒜 ∧ M.toBlocks₂₂ ∈ 𝒜}
  add_mem' := by
    rintro M N ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    exact ⟨𝒜.add_mem h1 h1', 𝒜.add_mem h2 h2', 𝒜.add_mem h3 h3', 𝒜.add_mem h4 h4'⟩
  zero_mem' := ⟨𝒜.zero_mem, 𝒜.zero_mem, 𝒜.zero_mem, 𝒜.zero_mem⟩
  smul_mem' := by
    rintro c M ⟨h1, h2, h3, h4⟩
    exact ⟨𝒜.smul_mem c h1, 𝒜.smul_mem c h2, 𝒜.smul_mem c h3, 𝒜.smul_mem c h4⟩

theorem fromBlocks_mem_blockAlg {A B C D : Matrix n n ℂ} :
    fromBlocks A B C D ∈ blockAlg 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ 𝒜 ∧ C ∈ 𝒜 ∧ D ∈ 𝒜 := by
  show (fromBlocks A B C D).toBlocks₁₁ ∈ 𝒜 ∧ _ ↔ _
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]

theorem isStarAlg_blockAlg (h𝒜 : IsStarAlg 𝒜) : IsStarAlg (blockAlg 𝒜) where
  one_mem := by
    rw [← fromBlocks_one, fromBlocks_mem_blockAlg]
    exact ⟨h𝒜.one_mem, 𝒜.zero_mem, 𝒜.zero_mem, h𝒜.one_mem⟩
  mul_mem := by
    intro M N hM hN
    rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N] at *
    rw [fromBlocks_mem_blockAlg] at hM hN
    obtain ⟨a, b, c, d⟩ := hM
    obtain ⟨a', b', c', d'⟩ := hN
    rw [fromBlocks_multiply, fromBlocks_mem_blockAlg]
    exact ⟨𝒜.add_mem (h𝒜.mul_mem a a') (h𝒜.mul_mem b c'),
      𝒜.add_mem (h𝒜.mul_mem a b') (h𝒜.mul_mem b d'),
      𝒜.add_mem (h𝒜.mul_mem c a') (h𝒜.mul_mem d c'),
      𝒜.add_mem (h𝒜.mul_mem c b') (h𝒜.mul_mem d d')⟩
  star_mem := by
    intro M hM
    rw [← fromBlocks_toBlocks M] at *
    rw [fromBlocks_mem_blockAlg] at hM
    obtain ⟨a, b, c, d⟩ := hM
    rw [fromBlocks_conjTranspose, fromBlocks_mem_blockAlg]
    exact ⟨h𝒜.star_mem a, h𝒜.star_mem c, h𝒜.star_mem b, h𝒜.star_mem d⟩

theorem hs_fromBlocks (A B C D A' B' C' D' : Matrix n n ℂ) :
    hs (fromBlocks A B C D) (fromBlocks A' B' C' D') = hs A A' + hs B B' + (hs C C' + hs D D') := by
  simp only [hs, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

theorem fromBlocks_sub' (A B C D A' B' C' D' : Matrix n n ℂ) :
    fromBlocks A B C D - fromBlocks A' B' C' D' = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> rfl

/-- The projection onto the block algebra acts blockwise. -/
theorem isHSProj_fromBlocks {Y₁₁ Y₁₂ Y₂₁ Y₂₂ Z₁₁ Z₁₂ Z₂₁ Z₂₂ : Matrix n n ℂ}
    (h₁₁ : IsHSProj 𝒜 Y₁₁ Z₁₁) (h₁₂ : IsHSProj 𝒜 Y₁₂ Z₁₂) (h₂₁ : IsHSProj 𝒜 Y₂₁ Z₂₁)
    (h₂₂ : IsHSProj 𝒜 Y₂₂ Z₂₂) :
    IsHSProj (blockAlg 𝒜) (fromBlocks Y₁₁ Y₁₂ Y₂₁ Y₂₂) (fromBlocks Z₁₁ Z₁₂ Z₂₁ Z₂₂) := by
  refine ⟨fromBlocks_mem_blockAlg.mpr ⟨h₁₁.1, h₁₂.1, h₂₁.1, h₂₂.1⟩, fun M hM => ?_⟩
  rw [← fromBlocks_toBlocks M] at hM ⊢
  rw [fromBlocks_mem_blockAlg] at hM
  obtain ⟨a, b, c, d⟩ := hM
  rw [fromBlocks_sub', hs_fromBlocks, h₁₁.2 _ a, h₁₂.2 _ b, h₂₁.2 _ c, h₂₂.2 _ d]
  simp

/-- **2-positivity.** Blockwise projection onto a unital `*`-subalgebra maps PSD 2×2 block
matrices to PSD block matrices. -/
theorem posSemidef_fromBlocks_of_isHSProj (h𝒜 : IsStarAlg 𝒜)
    {Y₁₁ Y₁₂ Y₂₁ Y₂₂ Z₁₁ Z₁₂ Z₂₁ Z₂₂ : Matrix n n ℂ}
    (h₁₁ : IsHSProj 𝒜 Y₁₁ Z₁₁) (h₁₂ : IsHSProj 𝒜 Y₁₂ Z₁₂) (h₂₁ : IsHSProj 𝒜 Y₂₁ Z₂₁)
    (h₂₂ : IsHSProj 𝒜 Y₂₂ Z₂₂) (hY : (fromBlocks Y₁₁ Y₁₂ Y₂₁ Y₂₂).PosSemidef) :
    (fromBlocks Z₁₁ Z₁₂ Z₂₁ Z₂₂).PosSemidef :=
  (isHSProj_fromBlocks h₁₁ h₁₂ h₂₁ h₂₂).posSemidef (isStarAlg_blockAlg h𝒜) hY

/-! ### Transport -/

/-- Transport of the projection along a map that preserves subtraction and orthogonality and
carries `𝒜` onto `𝒜'`. -/
theorem IsHSProj.map {m : Type*} [Fintype m] [DecidableEq m] {𝒜' : Submodule ℂ (Matrix m m ℂ)}
    (φ : Matrix n n ℂ → Matrix m m ℂ) (hsub : ∀ Y Z, φ (Y - Z) = φ Y - φ Z)
    (horth : ∀ A B, hs A B = 0 → hs (φ A) (φ B) = 0) (hmem : ∀ A ∈ 𝒜, φ A ∈ 𝒜')
    (hsurj : ∀ A' ∈ 𝒜', ∃ A ∈ 𝒜, φ A = A') {Y Z : Matrix n n ℂ} (h : IsHSProj 𝒜 Y Z) :
    IsHSProj 𝒜' (φ Y) (φ Z) := by
  refine ⟨hmem _ h.1, fun A' hA' => ?_⟩
  obtain ⟨A, hA, rfl⟩ := hsurj A' hA'
  rw [← hsub]
  exact horth _ _ (h.2 A hA)

/-- Entry rearrangements by a bijection of index pairs preserve the inner product. -/
theorem hs_reindex {m : Type*} [Fintype m] (F : m × m ≃ n × n) (A B : Matrix n n ℂ) :
    ∑ x, ∑ y, star (A (F (x, y)).1 (F (x, y)).2) * B (F (x, y)).1 (F (x, y)).2 = hs A B := by
  rw [← Fintype.sum_prod_type' (fun x y => star (A (F (x, y)).1 (F (x, y)).2) *
    B (F (x, y)).1 (F (x, y)).2)]
  rw [Equiv.sum_comp F (fun p => star (A p.1 p.2) * B p.1 p.2), hs]
  exact Fintype.sum_prod_type' (fun i j => star (A i j) * B i j)

/-- Entrywise conjugation conjugates the inner product. -/
theorem hs_map_star (A B : Matrix n n ℂ) : hs (A.map star) (B.map star) = star (hs A B) := by
  simp only [hs, Matrix.map_apply, star_sum, star_mul']

end HS

end WernerEndpoint

end

#print axioms WernerEndpoint.exists_isHSProj
#print axioms WernerEndpoint.IsHSProj.unique
#print axioms WernerEndpoint.IsHSProj.trace_mul
#print axioms WernerEndpoint.IsHSProj.isHermitian
#print axioms WernerEndpoint.IsHSProj.mul_left
#print axioms WernerEndpoint.IsHSProj.mul_right
#print axioms WernerEndpoint.IsHSProj.sum
#print axioms WernerEndpoint.IsHSProj.posSemidef
#print axioms WernerEndpoint.isStarAlg_blockAlg
#print axioms WernerEndpoint.isHSProj_fromBlocks
#print axioms WernerEndpoint.posSemidef_fromBlocks_of_isHSProj
#print axioms WernerEndpoint.IsHSProj.map
#print axioms WernerEndpoint.hs_reindex
#print axioms WernerEndpoint.hs_map_star
