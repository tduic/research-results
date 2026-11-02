import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import WernerEndpoint.LayerB_Basic

/-!
# L2: the lift and normalisation (layer B of `exact_certificate_d5/LEAN_PLAN.md`)

For a Fintype `H` with `|H| ≥ 2` (later `H = Fin 3 → Fin 5`) and `C : Matrix H H ℂ` of rank `≤ 2`
(rank one included) scaled to `‖C‖²_F = 1/2`, `lift_exists` produces `a b : H × Fin 2 → ℂ` with

* `C x y = ∑_r a (x, r) * conj (b (y, r))`, i.e. `C = ∑_r |a_r⟩⟨b_r|`;
* `∑_x a (x, r) * conj (a (x, r')) = δ_{rr'} / 2`, i.e. `Tr_H |a⟩⟨a| = I₂ / 2`;
* `‖a‖² = ‖b‖² = 1`.

Construction (Zenodo Lemma 2 / REVIEW §2 step 1): take two orthonormal vectors `ε₀, ε₁` whose span
contains the column space of `C` (`exists_orthonormal_cols`; when `rank C < 2` the pair is completed
inside `ℂ^H`, which needs `|H| ≥ 2`), so `C = A A* C` with the isometry `A = [ε₀ ε₁]`.  Then
`a = A / √2` and `b = √2 · C* A`.

Homogeneity of `q` is `qfun_smul` in `L1_Swap.lean`; the scaling step from a general nonzero `C`
is `qfun_nonneg_of_normalized` in `LayerB_Reduction.lean`.
-/

open Matrix Module
open scoped InnerProductSpace

noncomputable section

namespace WernerEndpoint

section Orthonormal

/-- In a finite-dimensional inner product space of dimension `≥ 2`, every subspace of
dimension `≤ 2` lies in the span of an orthonormal pair. -/
theorem exists_orthonormal_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (V : Submodule ℂ E) (hV : finrank ℂ V ≤ 2)
    (hE : 2 ≤ finrank ℂ E) :
    ∃ e : Fin 2 → E, Orthonormal ℂ e ∧ V ≤ Submodule.span ℂ (Set.range e) := by
  classical
  let bV := stdOrthonormalBasis ℂ V
  let w : Fin (finrank ℂ V) → E := fun j => (bV j : E)
  have hw : Orthonormal ℂ w := bV.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hset : Orthonormal ℂ ((↑) : Set.range w → E) := by
    exact (orthonormal_subtype_range hw.linearIndependent.injective).2 hw
  obtain ⟨u, b, hsub, hb⟩ := hset.exists_orthonormalBasis_extension
  have hcard : finrank ℂ E = u.card := by
    rw [Module.finrank_eq_card_basis b.toBasis]
    simp
  let W : Finset E := Finset.univ.image w
  have hWu : W ⊆ u := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact hsub (Set.mem_range_self j)
  have hWcard : W.card ≤ 2 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hV
  obtain ⟨T, hWT, hTu, hTcard⟩ : ∃ T : Finset E, W ⊆ T ∧ T ⊆ u ∧ T.card = 2 := by
    exact Finset.exists_subsuperset_card_eq hWu hWcard (by omega)
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → T, Function.Bijective g := by
    exact ⟨_, (T.equivFinOfCardEq hTcard).symm.bijective⟩
  have hu : Orthonormal ℂ ((↑) : u → E) := by
    rw [← hb]; exact b.orthonormal
  let f : Fin 2 → u := fun j => ⟨(g j : E), hTu (g j).2⟩
  have hf : Function.Injective f := by
    intro j j' h
    apply hg.1
    have h0 := congrArg Subtype.val h
    exact Subtype.ext h0
  refine ⟨fun j => (g j : E), hu.comp f hf, ?_⟩
  intro v hv
  have hrepr := congrArg Subtype.val (bV.sum_repr ⟨v, hv⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hrepr
  rw [← hrepr]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨j, hj⟩ := hg.2 ⟨w i, hWT (Finset.mem_image_of_mem w (Finset.mem_univ i))⟩
  exact Set.mem_range.mpr ⟨j, congrArg Subtype.val hj⟩

/-- The identification of `EuclideanSpace ℂ H` with functions `H → ℂ`. -/
noncomputable def eucl (H : Type*) [Fintype H] : EuclideanSpace ℂ H ≃ₗ[ℂ] (H → ℂ) :=
  WithLp.linearEquiv 2 ℂ (H → ℂ)

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem inner_eucl (x y : EuclideanSpace ℂ H) :
    ⟪x, y⟫_ℂ = ∑ i, star (eucl H x i) * eucl H y i := by
  unfold eucl
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- **L2 (isometry).** If `rank C ≤ 2` and `|H| ≥ 2`, there are orthonormal `ε₀, ε₁ ∈ ℂ^H` with
`C = ∑_j |ε_j⟩⟨ε_j| C`. -/
theorem exists_orthonormal_cols (C : Matrix H H ℂ) (hrank : C.rank ≤ 2)
    (hH : 2 ≤ Fintype.card H) :
    ∃ ε : Fin 2 → H → ℂ, (∀ j k, ∑ x, star (ε j x) * ε k x = if j = k then 1 else 0) ∧
      ∀ x y, C x y = ∑ j, ε j x * ∑ x', star (ε j x') * C x' y := by
  classical
  let V : Submodule ℂ (EuclideanSpace ℂ H) :=
    (LinearMap.range C.mulVecLin).map ((eucl H).symm : (H → ℂ) →ₗ[ℂ] EuclideanSpace ℂ H)
  have hV : finrank ℂ V ≤ 2 := by
    calc finrank ℂ V = finrank ℂ (LinearMap.range C.mulVecLin) :=
          LinearEquiv.finrank_map_eq (eucl H).symm _
      _ = C.rank := by rfl
      _ ≤ 2 := hrank
  have hE : 2 ≤ finrank ℂ (EuclideanSpace ℂ H) := by
    rw [finrank_euclideanSpace]
    exact hH
  obtain ⟨e, he, hVe⟩ := exists_orthonormal_pair V hV hE
  refine ⟨fun j => eucl H (e j), ?_, ?_⟩
  · intro j k
    dsimp only
    rw [← inner_eucl]
    exact orthonormal_iff_ite.mp he j k
  · intro x y
    dsimp only
    have hcol : (eucl H).symm (fun x' => C x' y) ∈ V := by
      refine Submodule.mem_map.mpr ⟨fun x' => C x' y, LinearMap.mem_range.mpr ⟨Pi.single y 1, ?_⟩, rfl⟩
      funext x'
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    obtain ⟨c, hc⟩ : ∃ c : Fin 2 → ℂ, ∑ i, c i • e i = (eucl H).symm (fun x' => C x' y) := by
      exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hVe hcol)
    have hci : ∀ j, c j = ⟪e j, (eucl H).symm (fun x' => C x' y)⟫_ℂ := by
      intro j
      rw [← hc]
      exact (he.inner_right_fintype c j).symm
    have hev := congrArg (fun v => eucl H v x) hc
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hev
    rw [← hev]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hci j, inner_eucl, LinearEquiv.apply_symm_apply]
    ring

end Orthonormal

section Lift

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **L2 (lift).** A rank-`≤ 2` operator `C ≠ 0` on `ℂ^H` (`|H| ≥ 2`), scaled to `‖C‖²_F = 1/2`,
lifts to `a b : H × Fin 2 → ℂ` with `C = ∑_r |a_r⟩⟨b_r|`, `Tr_H |a⟩⟨a| = I₂/2` and
`‖a‖ = ‖b‖ = 1`.  Rank one is included (the isometry is completed inside `ℂ^H`). -/
theorem lift_exists (C : Matrix H H ℂ) (hrank : C.rank ≤ 2) (hH : 2 ≤ Fintype.card H)
    (hnorm : frobSq C = 1 / 2) :
    ∃ a b : H × Fin 2 → ℂ,
      (∀ x y, C x y = ∑ r, a (x, r) * star (b (y, r))) ∧
      (∀ r r', ∑ x, a (x, r) * star (a (x, r')) = if r = r' then (1 / 2 : ℂ) else 0) ∧
      vnormSq a = 1 ∧ vnormSq b = 1 := by
  obtain ⟨ε, hon, hexp⟩ := exists_orthonormal_cols C hrank hH
  obtain ⟨B, hB⟩ : ∃ B : Fin 2 → H → ℂ, ∀ r y, B r y = ∑ x', star (ε r x') * C x' y :=
    ⟨_, fun _ _ => rfl⟩
  have hexp' : ∀ x y, C x y = ∑ r, ε r x * B r y := fun x y => by
    simp only [hB]
    exact hexp x y
  obtain ⟨σ, hσr⟩ : ∃ σ : ℝ, σ * σ = 1 / 2 :=
    ⟨Real.sqrt (1 / 2), Real.mul_self_sqrt (by norm_num)⟩
  have hσ : (σ : ℂ) * σ = 1 / 2 := by
    rw [← Complex.ofReal_mul, hσr]
    norm_num
  have parseval : ∀ y, ∑ x, star (C x y) * C x y = ∑ r, star (B r y) * B r y := by
    intro y
    have h1 : ∀ r, ∑ x, star (C x y) * ε r x = star (B r y) := by
      intro r
      rw [hB, star_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_mul', star_star, mul_comm]
    calc ∑ x, star (C x y) * C x y = ∑ x, ∑ r, star (C x y) * (ε r x * B r y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, ← hexp' x y]
      _ = ∑ r, (∑ x, star (C x y) * ε r x) * B r y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = ∑ r, star (B r y) * B r y := Finset.sum_congr rfl fun r _ => by rw [h1 r]
  refine ⟨fun p => (σ : ℂ) * ε p.2 p.1, fun p => ((2 * σ : ℝ) : ℂ) * star (B p.2 p.1),
    ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [hexp' x y]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only
    rw [star_mul', star_ofReal', star_star]
    push_cast
    linear_combination (-2 * ε r x * B r y) * hσ
  · intro r r'
    dsimp only
    have h1 : ∑ x, (σ : ℂ) * ε r x * star ((σ : ℂ) * ε r' x) =
        ((σ : ℂ) * σ) * ∑ x, star (ε r' x) * ε r x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_mul', star_ofReal']
      ring
    rw [h1, hon r' r, hσ]
    by_cases h : r = r'
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · apply Complex.ofReal_injective
    rw [ofReal_vnormSq, nsqC]
    rw [Fintype.sum_prod_type_right]
    dsimp only
    have h2 : ∀ r : Fin 2, ∑ x, star ((σ : ℂ) * ε r x) * ((σ : ℂ) * ε r x) = 1 / 2 := by
      intro r
      calc ∑ x, star ((σ : ℂ) * ε r x) * ((σ : ℂ) * ε r x)
          = ((σ : ℂ) * σ) * ∑ x, star (ε r x) * ε r x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [star_mul', star_ofReal']
            ring
        _ = 1 / 2 := by rw [hon r r, if_pos rfl, hσ, mul_one]
    rw [Finset.sum_congr rfl fun r _ => h2 r]
    norm_num [Fin.sum_univ_two]
  · apply Complex.ofReal_injective
    rw [ofReal_vnormSq, nsqC, Fintype.sum_prod_type]
    dsimp only
    have hterm : ∀ y (r : Fin 2),
        star (((2 * σ : ℝ) : ℂ) * star (B r y)) * (((2 * σ : ℝ) : ℂ) * star (B r y)) =
          4 * ((σ : ℂ) * σ) * (star (B r y) * B r y) := by
      intro y r
      rw [star_mul', star_ofReal', star_star]
      push_cast
      ring
    have hsum : ∑ y, ∑ r : Fin 2, star (B r y) * B r y = 1 / 2 := by
      calc ∑ y, ∑ r : Fin 2, star (B r y) * B r y = ∑ y, ∑ x, star (C x y) * C x y :=
            Finset.sum_congr rfl fun y _ => (parseval y).symm
        _ = ∑ x, ∑ y, star (C x y) * C x y := Finset.sum_comm
        _ = ((frobSq C : ℝ) : ℂ) := (ofReal_frobSq C).symm
        _ = 1 / 2 := by
            rw [hnorm]
            norm_num
    rw [Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r _ => hterm y r]
    simp only [← Finset.mul_sum]
    rw [hsum, hσ]
    norm_num

end Lift

end WernerEndpoint

end

#print axioms WernerEndpoint.exists_orthonormal_pair
#print axioms WernerEndpoint.inner_eucl
#print axioms WernerEndpoint.exists_orthonormal_cols
#print axioms WernerEndpoint.lift_exists
