import WernerEndpoint.AllD_Blocks

/-!
# All-d lemma chain, step 5 / item 5: the coupled blocks (full 2×2 operator)

For a coupled block (cut `T`, three rearrangements `σ₃₁, σ₂₂, σ₁₃` with diagram maps
`m₃₁, m₂₂, m₁₃`) the full operator in module coordinates is

  `[[L₃₁, L₂₂], [L₂₂ᵀ, L₁₃]]`,  `L_f = blockOp N Fq m_f (μ_f)`

(`blockOp` of `AllD_Blocks.lean`; this is the verifier's `F[np.ix_(m,m,m,m)]` contracted with the
site and qubit modules). **`blockOp_coupled_posSemidef_of`**: at every `d ≥ 4`, for every
trace-coordinate vector `μ` of every `a, b` at local dimension `d`, this operator is PSD. Hence
so is every stacked compression `[Bu; Bv]ᵀ (·) [Bu; Bv]` (`fromRows_compress` with `conjTranspose_mul_mul_same`), which
expands to `Buᵀ L₃₁ Bu + Buᵀ L₂₂ Bv + Bvᵀ L₂₂ᵀ Bu + Bvᵀ L₁₃ Bv` (`fromRows_compress`).

Proof: layer C's 2-positivity (`twirl_coupled_T*_posSemidef`) gives the physical 2×2 block PSD;
it is a sum `∑_u (⊗_i Γ_T(P_{u_i})) ⊗ R_u` with `R_u` a 2×2 block matrix on the qubit space;
complete positivity of the site modules (`cp_sites`, applied with auxiliary space `W ⊕ W`), the
qubit compression `J ⊕ J` and the Weingarten step for each family (the maps preserve `G_d`,
item 4) give the module operator; its `(2,1)` block is the adjoint of the `(1,2)` block because
the whole operator is Hermitian.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Coupled

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A surjective table map as a bijection of `S₄`. -/
def mpE (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) : P4 ≃ P4 :=
  Equiv.ofBijective (permMap m) (permMap_bijective hm)

theorem mpE_apply (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) (p : P4) :
    mpE m hm p = permMap m p := rfl

/-- Block decomposition of a sum of `gtens` with a 2×2 block coefficient. -/
theorem gtens_sum_fromBlocks {K : κ → Type*} [∀ i, Fintype (K i)] {W β : Type*} [Fintype W]
    [Fintype β] (A : β → (i : κ) → Matrix (K i) (K i) ℂ) (R₁ R₂ R₃ R₄ : β → Matrix W W ℂ) :
    (∑ u, gtens (K := K) (K' := K) (A u) (fromBlocks (R₁ u) (R₂ u) (R₃ u) (R₄ u))).submatrix
        (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm =
      fromBlocks (∑ u, gtens (A u) (R₁ u)) (∑ u, gtens (A u) (R₂ u)) (∑ u, gtens (A u) (R₃ u))
        (∑ u, gtens (A u) (R₄ u)) := by
  ext (⟨X, w⟩ | ⟨X, w⟩) (⟨Y, w'⟩ | ⟨Y, w'⟩) <;>
    simp [gtens, Matrix.sum_apply, Equiv.prodSumDistrib]

theorem fromBlocks_submatrix_same {X Z : Type*} (s : X → Z) (A B C D : Matrix Z Z ℂ) :
    fromBlocks (A.submatrix s s) (B.submatrix s s) (C.submatrix s s) (D.submatrix s s) =
      (fromBlocks A B C D).submatrix (Sum.map s s) (Sum.map s s) := by
  ext (i | i) (j | j) <;> rfl

theorem rearr_sum_smul (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) {ι ρ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] (y : Tup κ → ℝ) :
    rearr σ (∑ t, ((y t : ℝ) : ℂ) • permOp ι ρ t.1 t.2) =
      ∑ t, ((y t : ℝ) : ℂ) • rearr σ (permOp ι ρ t.1 t.2) := by
  show rearrL κ ι ρ σ _ = _
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- The physical rearranged twirl in `tensO` form. -/
theorem rearr_twirl_eq {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)}
    (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j)
    (hι : ∀ i, rearr σ (sP (Fin d) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin d) T (sP (Fin d) (permTab (m i))))
    (hρ : ∀ i, rearr σ (sP (Fin 2) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin 2) T (sP (Fin 2) (permTab (m i))))
    {a b : (κ → Fin d) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) (f : Fam) :
    rearr σ (twirl f a b) =
      (∑ u, tensO (Osite T (Fin d)) u (Rphys T (Fin 2) (mpE m hm) (siteWg d (μ f)) u)).submatrix
        splitX splitX := by
  rw [(rep_of_mcoord hd hμ f).1, rearr_sum_smul, ← phys_eq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rearr_permOp_of_sites σ T m hι hρ t]
  rfl

/-- The `(2,1)` coefficient: the adjoint of a `tensO` sum is a `tensO` sum. -/
theorem tensO_sum_conjTranspose {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)} {tab : P4 → P4 → P4 × ℕ}
    (htab : TabAt T d tab) {W : Type*} [Fintype W] [DecidableEq W] (R : (κ → P4) → Matrix W W ℂ) :
    (∑ u, tensO (Osite T (Fin d)) u (R u))ᴴ =
      ∑ u, tensO (Osite T (Fin d)) u (R (fun i => (u i)⁻¹))ᴴ := by
  rw [conjTranspose_sum]
  simp only [tensO_conjTranspose (diagFamily_site hd htab)]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : κ => Equiv.inv P4) _ _ fun u => ?_
  have h1 : (Equiv.piCongrRight fun _ : κ => Equiv.inv P4) u = fun i => (u i)⁻¹ := rfl
  rw [h1]
  simp only [inv_inv]

theorem cmap_fromBlocks {n : Type*} (A B C D : Matrix n n ℝ) :
    fromBlocks (cmap A) (cmap B) (cmap C) (cmap D) = cmap (fromBlocks A B C D) := by
  ext (i | i) (j | j) <;> rfl

/-- **Item 5, coupled blocks (full operator), generic form.** -/
theorem blockOp_coupled_posSemidef_of {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)}
    {tab : P4 → P4 → P4 × ℕ} (htab : TabAt T d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J)
    (σ₁ σ₂ σ₃ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (m₁ m₂ m₃ : Fin 24 → Fin 24)
    (s₁ : ∀ j, ∃ i, m₁ i = j) (s₂ : ∀ j, ∃ i, m₂ i = j) (s₃ : ∀ j, ∃ i, m₃ i = j)
    (h₁ι : ∀ i, rearr σ₁ (sP (Fin d) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin d) T (sP (Fin d) (permTab (m₁ i))))
    (h₁ρ : ∀ i, rearr σ₁ (sP (Fin 2) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin 2) T (sP (Fin 2) (permTab (m₁ i))))
    (h₂ι : ∀ i, rearr σ₂ (sP (Fin d) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin d) T (sP (Fin d) (permTab (m₂ i))))
    (h₂ρ : ∀ i, rearr σ₂ (sP (Fin 2) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin 2) T (sP (Fin 2) (permTab (m₂ i))))
    (h₃ι : ∀ i, rearr σ₃ (sP (Fin d) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin d) T (sP (Fin d) (permTab (m₃ i))))
    (h₃ρ : ∀ i, rearr σ₃ (sP (Fin 2) (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => Fin 2) T (sP (Fin 2) (permTab (m₃ i))))
    (hg₁ : ∀ a b, gram d (mpE m₁ s₁ a) (mpE m₁ s₁ b) = gram d a b)
    (hg₂ : ∀ a b, gram d (mpE m₂ s₂ a) (mpE m₂ s₂ b) = gram d a b)
    (hg₃ : ∀ a b, gram d (mpE m₃ s₃ a) (mpE m₃ s₃ b) = gram d a b)
    {a b : (κ → Fin d) × Fin 2 → ℂ}
    (hphys : (fromBlocks (rearr σ₁ (twirl .f31 a b)) (rearr σ₂ (twirl .f22 a b))
      (rearr σ₂ (twirl .f22 a b))ᴴ (rearr σ₃ (twirl .f13 a b))).PosSemidef)
    {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    (fromBlocks (blockOp N Fq (mpE m₁ s₁) (μ .f31)) (blockOp N Fq (mpE m₂ s₂) (μ .f22))
      (blockOp N Fq (mpE m₂ s₂) (μ .f22))ᵀ (blockOp N Fq (mpE m₃ s₃) (μ .f13))).PosSemidef := by
  -- the physical block as a `tensO` sum with block coefficients
  rw [rearr_twirl_eq hd σ₁ m₁ s₁ h₁ι h₁ρ hμ, rearr_twirl_eq hd σ₂ m₂ s₂ h₂ι h₂ρ hμ,
    rearr_twirl_eq hd σ₃ m₃ s₃ h₃ι h₃ρ hμ, conjTranspose_submatrix,
    tensO_sum_conjTranspose hd htab, fromBlocks_submatrix_same,
    ← gtens_sum_fromBlocks (K := fun _ : κ => Fin 4 → Fin d), submatrix_submatrix] at hphys
  have hR := (posSemidef_submatrix_equiv
    ((Equiv.sumCongr splitX splitX).trans (Equiv.prodSumDistrib _ _ _).symm)).mp hphys
  -- complete positivity, then the qubit compression `J ⊕ J`
  have h1 := cp_sites hd htab F hF _ hR
  set Jb : Matrix ((Fin 4 → Fin 2) ⊕ (Fin 4 → Fin 2)) (Kq ⊕ Kq) ℂ :=
    fromBlocks (cmap J) 0 0 (cmap J)
  have h2 := h1.conjTranspose_mul_mul_same (gtens (K := K) (K' := K) (fun _ => 1) Jb)
  rw [compress_sum] at h2
  have hJb : ∀ A B C D : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ,
      Jbᴴ * fromBlocks A B C D * Jb =
      fromBlocks ((cmap J)ᴴ * A * cmap J) ((cmap J)ᴴ * B * cmap J)
        ((cmap J)ᴴ * C * cmap J) ((cmap J)ᴴ * D * cmap J) := by
    intro A B C D
    simp only [Jb, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  simp only [hJb] at h2
  rw [← posSemidef_submatrix_equiv (Equiv.prodSumDistrib _ _ _).symm, gtens_sum_fromBlocks,
    module_block_eq F N c hc hW hJ _ hg₁ _ _ (siteG_siteWg hd _),
    module_block_eq F N c hc hW hJ _ hg₂ _ _ (siteG_siteWg hd _),
    module_block_eq F N c hc hW hJ _ hg₃ _ _ (siteG_siteWg hd _)] at h2
  -- the `(2,1)` block is the adjoint of the `(1,2)` block
  set s : ℝ := ∏ i, (c i)⁻¹
  have hs : 0 < s := Finset.prod_pos fun i _ => inv_pos.mpr (hc i)
  set L₁ := blockOp N Fq (mpE m₁ s₁) (μ .f31)
  set L₂ := blockOp N Fq (mpE m₂ s₂) (μ .f22)
  set L₃ := blockOp N Fq (mpE m₃ s₃) (μ .f13)
  have hH := h2.isHermitian
  unfold Matrix.IsHermitian at hH
  rw [fromBlocks_conjTranspose] at hH
  have h21 := (fromBlocks_inj.mp hH).2.1
  have hC := congrArg conjTranspose h21
  rw [conjTranspose_conjTranspose] at hC
  rw [hC, cmap_conjTranspose, cmap_fromBlocks] at h2
  have h3 := (posSemidef_of_cmap h2).smul (inv_pos.mpr hs).le
  convert h3 using 1
  rw [transpose_smul, ← fromBlocks_smul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- **Item 5, coupled block `T = {3}`** (`MAPS["c3"]`), full operator. -/
theorem blockOp_coupled_T3_posSemidef {d : ℕ} (hd : 4 ≤ d) {tab : P4 → P4 → P4 × ℕ}
    (htab : TabAt {3} d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt {3} Fq J)
    {a b : (κ → Fin d) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    (fromBlocks (blockOp N Fq (mpE mT3_31 mT3_31_surj) (μ .f31))
      (blockOp N Fq (mpE mT3_22 mT3_22_surj) (μ .f22))
      (blockOp N Fq (mpE mT3_22 mT3_22_surj) (μ .f22))ᵀ
      (blockOp N Fq (mpE mT3_13 mT3_13_surj) (μ .f13))).PosSemidef := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  exact blockOp_coupled_posSemidef_of hd htab F N hF c hc hW hJ _ _ _ _ _ _ _ _ _
    (rearr_sP_T3_31 _) (rearr_sP_T3_31 _) (rearr_sP_T3_22 _) (rearr_sP_T3_22 _)
    (rearr_sP_T3_13 _) (rearr_sP_T3_13 _)
    (gram_permMap_T3_31 d) (gram_permMap_T3_22 d) (gram_permMap_T3_13 d)
    (twirl_coupled_T3_posSemidef a b) hμ

/-- **Item 5, coupled block `T = {2,3}`** (`MAPS["c23"]`), full operator. -/
theorem blockOp_coupled_T23_posSemidef {d : ℕ} (hd : 4 ≤ d) {tab : P4 → P4 → P4 × ℕ}
    (htab : TabAt {2, 3} d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt {2, 3} Fq J)
    {a b : (κ → Fin d) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) :
    (fromBlocks (blockOp N Fq (mpE mT23_31 mT23_31_surj) (μ .f31))
      (blockOp N Fq (mpE mT23_22 mT23_22_surj) (μ .f22))
      (blockOp N Fq (mpE mT23_22 mT23_22_surj) (μ .f22))ᵀ
      (blockOp N Fq (mpE mT23_13 mT23_13_surj) (μ .f13))).PosSemidef := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  exact blockOp_coupled_posSemidef_of hd htab F N hF c hc hW hJ _ _ _ _ _ _ _ _ _
    (rearr_sP_T23_31 _) (rearr_sP_T23_31 _) (rearr_sP_T23_22 _) (rearr_sP_T23_22 _)
    (rearr_sP_T23_13 _) (rearr_sP_T23_13 _)
    (gram_permMap_T23_31 d) (gram_permMap_T23_22 d) (gram_permMap_T23_13 d)
    (twirl_coupled_T23_posSemidef a b) hμ

/-- The stacked compression expands to the verifier's four terms. -/
theorem fromRows_compress {n k : Type*} [Fintype n] (A B C D : Matrix n n ℝ)
    (Bu Bv : Matrix n k ℝ) :
    (fromRows Bu Bv)ᵀ * fromBlocks A B C D * fromRows Bu Bv =
      Buᵀ * A * Bu + Buᵀ * B * Bv + Bvᵀ * C * Bu + Bvᵀ * D * Bv := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
    fromRows_apply_inl, fromRows_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, add_mul, Finset.sum_add_distrib]
  ring

end Coupled

end WernerEndpoint

end

#print axioms WernerEndpoint.gtens_sum_fromBlocks
#print axioms WernerEndpoint.rearr_twirl_eq
#print axioms WernerEndpoint.blockOp_coupled_posSemidef_of
#print axioms WernerEndpoint.blockOp_coupled_T3_posSemidef
#print axioms WernerEndpoint.blockOp_coupled_T23_posSemidef
#print axioms WernerEndpoint.fromRows_compress
