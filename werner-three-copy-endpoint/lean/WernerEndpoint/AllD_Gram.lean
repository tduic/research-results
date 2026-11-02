import WernerEndpoint.LayerC_Walled
import WernerEndpoint.LayerC_Sites

/-!
# All-d lemma chain: the one-site Gram matrix `G_d(p, q) = d^{cyc(p⁻¹ q)}`

One site of the four-replica space is `(ℂ^α)^{⊗4}`; `sP α p` is the permutation operator
(`(sP α p) x y = [y = x ∘ p]`) and `ptrans T` the partial transpose.

* `hs_sP_sP`: `⟨P_p, P_q⟩_HS = |α|^{cyc(p⁻¹ q)}` (cycles counted with fixed points), for every
  local dimension. `gram d p q = d^{cyc(p⁻¹ q)}` is the verifier's `G_d`.
* `cycCount_conj`, `cycCount_inv`, and the four invariances of `gram` (symmetry, left and right
  multiplication, inversion) used to show that the orbit generators commute with `G_d`.
* `dualEntry_ptrans_sP`: for `|α| ≥ 4` every partially transposed diagram `Γ_T(P_p)` has an entry
  at which it is `1` and every other `Γ_T(P_{p'})` is `0` (rows/columns of distinct digits). This is
  the linear independence of the 24 diagrams that the all-d argument needs (verifier (A1)), proved
  directly and for every `d ≥ 4`.
* `gram_isUnit`: `G_d` is invertible for `d ≥ 4` (`det G_d ≠ 0`).
* `cycCount_map_of_rearr` (**item 4 of the red team's list**): if a literal rearrangement `σ`
  sends every diagram to a partially transposed diagram, `rearr σ (P_p) = Γ_T(P_{m p})`, at a local
  dimension `≥ 2`, then `m` preserves `cyc(a⁻¹ b)` — because `rearr σ` and `Γ_T` are isometries
  of the Hilbert–Schmidt form. Hence `gram d (m a) (m b) = gram d a b` for every `d`. Applied to the
  six coupled-block maps of layer C (`gram_permMap_T3_31` … `gram_permMap_T23_22`).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Gram

abbrev P4 := Equiv.Perm (Fin 4)

/-! ### Fixed colourings under conjugation and inversion -/

theorem fixCount_conj (ι : Type*) [Fintype ι] [DecidableEq ι] (g p : P4) :
    fixCount ι (g * p * g⁻¹) = fixCount ι p := by
  unfold fixCount
  refine Fintype.card_congr
    { toFun := fun f => ⟨f.1 ∘ g, ?_⟩
      invFun := fun f => ⟨f.1 ∘ ⇑(g⁻¹), ?_⟩
      left_inv := fun f => Subtype.ext (funext fun x => by simp)
      right_inv := fun f => Subtype.ext (funext fun x => by simp) }
  · funext x
    have := congrFun f.2 (g x)
    simpa [Equiv.Perm.mul_apply] using this
  · funext x
    have := congrFun f.2 (g⁻¹ x)
    simp only [Function.comp_apply] at this ⊢
    rw [← this]
    simp [Equiv.Perm.mul_apply]

theorem fixCount_inv (ι : Type*) [Fintype ι] [DecidableEq ι] (p : P4) :
    fixCount ι p⁻¹ = fixCount ι p := by
  unfold fixCount
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  constructor
  · intro h
    funext x
    have := congrFun h (p x)
    simpa using this.symm
  · intro h
    funext x
    have := congrFun h (p⁻¹ x)
    simpa using this.symm

theorem cycCount_eq_of_fixCount {p q : P4} (h : fixCount (Fin 2) p = fixCount (Fin 2) q) :
    cycCount p = cycCount q := by
  rw [fixCount_eq_pow, fixCount_eq_pow, Fintype.card_fin] at h
  exact Nat.pow_right_injective le_rfl h

theorem cycCount_conj (g p : P4) : cycCount (g * p * g⁻¹) = cycCount p :=
  cycCount_eq_of_fixCount (fixCount_conj _ g p)

theorem cycCount_inv (p : P4) : cycCount p⁻¹ = cycCount p :=
  cycCount_eq_of_fixCount (fixCount_inv _ p)

/-! ### The Hilbert–Schmidt Gram matrix of one site -/

theorem hs_sP_sP (α : Type*) [Fintype α] [DecidableEq α] (p q : P4) :
    hs (sP α p) (sP α q) = ((Fintype.card α ^ cycCount (p⁻¹ * q) : ℕ) : ℂ) := by
  have h1 : hs (sP α p) (sP α q) = ((fixCount α (p * q⁻¹) : ℕ) : ℂ) := by
    simp only [hs, sP, Matrix.of_apply]
    have : ∀ x : Fin 4 → α, (∑ y : Fin 4 → α, star (if y = x ∘ p then (1 : ℂ) else 0) *
        (if y = x ∘ q then 1 else 0)) = if x ∘ (p * q⁻¹) = x then 1 else 0 := by
      intro x
      rw [Finset.sum_eq_single (x ∘ p)]
      · simp only [if_true, star_one, one_mul]
        congr 1
        apply propext
        constructor
        · intro h; funext k
          have := congrFun h (q⁻¹ k)
          simpa [Equiv.Perm.mul_apply] using this
        · intro h; funext k
          have := congrFun h (q k)
          simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self] at this
          exact this
      · intro y _ hy; simp [hy]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [this]
    rw [Finset.sum_boole, fixCount]
    simp only [Fintype.card_subtype]
  rw [h1]
  have h2 : fixCount α (p * q⁻¹) = fixCount α (p⁻¹ * q) := by
    have e : p⁻¹ * q = p⁻¹ * (q * p⁻¹) * p⁻¹⁻¹ := by group
    rw [e, fixCount_conj, ← fixCount_inv α (q * p⁻¹)]
    congr 1
  rw [h2, fixCount_eq_pow]

/-- The verifier's one-site Gram matrix `G_d(p, q) = d^{cyc(p⁻¹ q)}` (`MULI[INVI[a]][b]`). -/
def gram (d : ℕ) (p q : P4) : ℝ := (d : ℝ) ^ cycCount (p⁻¹ * q)

theorem hs_sP_sP_gram (d : ℕ) (p q : P4) :
    hs (sP (Fin d) p) (sP (Fin d) q) = (gram d p q : ℂ) := by
  rw [hs_sP_sP, gram, Fintype.card_fin]
  push_cast; rfl

theorem gram_symm (d : ℕ) (p q : P4) : gram d p q = gram d q p := by
  unfold gram
  rw [show q⁻¹ * p = (p⁻¹ * q)⁻¹ by group, cycCount_inv]

theorem gram_lmul (d : ℕ) (g p q : P4) : gram d (g * p) (g * q) = gram d p q := by
  unfold gram
  rw [show (g * p)⁻¹ * (g * q) = p⁻¹ * q by group]

theorem gram_rmul (d : ℕ) (g p q : P4) : gram d (p * g) (q * g) = gram d p q := by
  unfold gram
  rw [show (p * g)⁻¹ * (q * g) = g⁻¹ * (p⁻¹ * q) * g⁻¹⁻¹ by group, cycCount_conj]

theorem gram_inv (d : ℕ) (p q : P4) : gram d p⁻¹ q⁻¹ = gram d p q := by
  unfold gram
  rw [show p⁻¹⁻¹ * q⁻¹ = p * (q⁻¹ * p) * p⁻¹ by group, cycCount_conj,
    show q⁻¹ * p = (p⁻¹ * q)⁻¹ by group, cycCount_inv]

/-! ### Independence of the diagrams for `d ≥ 4` -/

theorem sP_apply_inj {α : Type*} [Fintype α] [DecidableEq α] {x0 : Fin 4 → α}
    (hx0 : Function.Injective x0) (p p' : P4) :
    sP α p' x0 (x0 ∘ p) = if p' = p then 1 else 0 := by
  simp only [sP, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · intro h
    ext k
    have := congrFun h k
    exact congrArg _ (hx0 this).symm
  · intro h; rw [h]

/-- **Dual entries.** For `|α| ≥ 4`, each `Γ_T(P_p)` has an entry where it is `1` and every
other `Γ_T(P_{p'})` vanishes. -/
theorem dualEntry_ptrans_sP (α : Type*) [Fintype α] [DecidableEq α] (hα : 4 ≤ Fintype.card α)
    (T : Finset (Fin 4)) (p : P4) :
    ∃ x y : Fin 4 → α, ∀ p' : P4,
      ptrans (ι := fun _ : Fin 4 => α) T (sP α p') x y = if p' = p then 1 else 0 := by
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ α) := Function.Embedding.nonempty_of_card_le (by simpa using hα)
  refine ⟨fun r => if r ∈ T then (e ∘ p) r else e r, fun r => if r ∈ T then e r else (e ∘ p) r,
    fun p' => ?_⟩
  have hx : (fun r => if r ∈ T then (fun r => if r ∈ T then e r else (e ∘ p) r) r
      else (fun r => if r ∈ T then (e ∘ p) r else e r) r) = (e : Fin 4 → α) := by
    funext r; by_cases h : r ∈ T <;> simp [h]
  have hy : (fun r => if r ∈ T then (fun r => if r ∈ T then (e ∘ p) r else e r) r
      else (fun r => if r ∈ T then e r else (e ∘ p) r) r) = (e : Fin 4 → α) ∘ p := by
    funext r; by_cases h : r ∈ T <;> simp [h]
  simp only [ptrans, Matrix.of_apply]
  rw [hx, hy]
  exact sP_apply_inj e.injective p p'

/-- `G_d` as a matrix. -/
def gramMat (d : ℕ) : Matrix P4 P4 ℝ := Matrix.of (gram d)

theorem hs_sum_sum {n ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι'] (A : ι' → Matrix n n ℂ) (a b : ι' → ℂ) :
    hs (∑ i, a i • A i) (∑ j, b j • A j) = ∑ i, ∑ j, star (a i) * b j * hs (A i) (A j) := by
  simp only [hs_eq_trace, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`G_d` is invertible for every `d ≥ 4`.** -/
theorem gram_isUnit {d : ℕ} (hd : 4 ≤ d) : IsUnit (gramMat d).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv0
  -- `vᵀ G v = ‖∑ v_p P_p‖² = 0`
  set A : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ := ∑ p, ((v p : ℝ) : ℂ) • sP (Fin d) p
  have hAA : hs A A = 0 := by
    rw [hs_sum_sum]
    have : ∀ p, ∑ q, star ((v p : ℝ) : ℂ) * ((v q : ℝ) : ℂ) * hs (sP (Fin d) p) (sP (Fin d) q) =
        ((v p * (gramMat d *ᵥ v) p : ℝ) : ℂ) := by
      intro p
      simp only [hs_sP_sP_gram, Complex.star_def, Complex.conj_ofReal, mulVec, dotProduct,
        gramMat, Matrix.of_apply, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun q _ => by ring
    simp only [this, hv, Pi.zero_apply, mul_zero, Complex.ofReal_zero, Finset.sum_const_zero]
  have hA : A = 0 := hs_self_eq_zero.mp hAA
  funext p
  obtain ⟨x, y, hxy⟩ := dualEntry_ptrans_sP (Fin d) (by simpa using hd) ∅ p
  have := congrFun (congrFun hA x) y
  simp only [A, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
  have e : ∀ p', sP (Fin d) p' x y = if p' = p then 1 else 0 := by
    intro p'
    have := hxy p'
    simpa [ptrans] using this
  simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact_mod_cast this

/-- The Weingarten matrix `Wg_d = G_d⁻¹`; `G_d Wg_d = Wg_d G_d = 1` for `d ≥ 4`. -/
def wg (d : ℕ) : Matrix P4 P4 ℝ := (gramMat d)⁻¹

theorem gram_mul_wg {d : ℕ} (hd : 4 ≤ d) : gramMat d * wg d = 1 :=
  Matrix.mul_nonsing_inv _ (gram_isUnit hd)

theorem wg_mul_gram {d : ℕ} (hd : 4 ≤ d) : wg d * gramMat d = 1 :=
  Matrix.nonsing_inv_mul _ (gram_isUnit hd)

/-! ### Item 4: the coupled diagram maps preserve `cyc(a⁻¹ b)` -/

/-- **Equivariance from L6 and the Hilbert–Schmidt isometry.** -/
theorem cycCount_map_of_rearr (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (T : Finset (Fin 4))
    (m : P4 → P4) (hm : ∀ p, rearr σ (sP (Fin 2) p) = ptrans (ι := fun _ : Fin 4 => Fin 2) T
      (sP (Fin 2) (m p))) (a b : P4) :
    cycCount ((m a)⁻¹ * m b) = cycCount (a⁻¹ * b) := by
  have h := hs_rearr σ (sP (Fin 2) a) (sP (Fin 2) b)
  rw [hm, hm, hs_ptrans, hs_sP_sP, hs_sP_sP, Fintype.card_fin] at h
  exact Nat.pow_right_injective le_rfl (by exact_mod_cast h)

theorem gram_map_of_rearr (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (T : Finset (Fin 4))
    (m : P4 → P4) (hm : ∀ p, rearr σ (sP (Fin 2) p) = ptrans (ι := fun _ : Fin 4 => Fin 2) T
      (sP (Fin 2) (m p))) (d : ℕ) (a b : P4) : gram d (m a) (m b) = gram d a b := by
  unfold gram; rw [cycCount_map_of_rearr σ T m hm]

theorem permMap_bijective {m : Fin 24 → Fin 24} (hm : ∀ j, ∃ i, m i = j) :
    Function.Bijective (permMap m) :=
  (Finite.injective_iff_surjective).mpr (permMap_surj hm) |> fun h => ⟨h, permMap_surj hm⟩

theorem gram_permMap_T3_31 (d : ℕ) (a b : P4) :
    gram d (permMap mT3_31 a) (permMap mT3_31 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T3_31 (Fin 2))) d a b
theorem gram_permMap_T3_13 (d : ℕ) (a b : P4) :
    gram d (permMap mT3_13 a) (permMap mT3_13 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T3_13 (Fin 2))) d a b
theorem gram_permMap_T3_22 (d : ℕ) (a b : P4) :
    gram d (permMap mT3_22 a) (permMap mT3_22 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T3_22 (Fin 2))) d a b
theorem gram_permMap_T23_31 (d : ℕ) (a b : P4) :
    gram d (permMap mT23_31 a) (permMap mT23_31 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T23_31 (Fin 2))) d a b
theorem gram_permMap_T23_13 (d : ℕ) (a b : P4) :
    gram d (permMap mT23_13 a) (permMap mT23_13 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T23_13 (Fin 2))) d a b
theorem gram_permMap_T23_22 (d : ℕ) (a b : P4) :
    gram d (permMap mT23_22 a) (permMap mT23_22 b) = gram d a b :=
  gram_map_of_rearr _ _ _ (rearr_sP_permMap _ _ _ (rearr_sP_T23_22 (Fin 2))) d a b

end Gram

end WernerEndpoint

end

#print axioms WernerEndpoint.fixCount_conj
#print axioms WernerEndpoint.cycCount_conj
#print axioms WernerEndpoint.cycCount_inv
#print axioms WernerEndpoint.hs_sP_sP
#print axioms WernerEndpoint.gram_symm
#print axioms WernerEndpoint.gram_lmul
#print axioms WernerEndpoint.gram_rmul
#print axioms WernerEndpoint.gram_inv
#print axioms WernerEndpoint.dualEntry_ptrans_sP
#print axioms WernerEndpoint.gram_isUnit
#print axioms WernerEndpoint.gram_mul_wg
#print axioms WernerEndpoint.cycCount_map_of_rearr
#print axioms WernerEndpoint.gram_map_of_rearr
#print axioms WernerEndpoint.gram_permMap_T3_31
#print axioms WernerEndpoint.gram_permMap_T23_22
