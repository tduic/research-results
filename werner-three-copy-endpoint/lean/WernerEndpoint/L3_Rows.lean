import WernerEndpoint.L4_WordPositivity
import WernerEndpoint.LayerB_Basic

/-!
# L3: row validity (layer B of `exact_certificate_d5/LEAN_PLAN.md`)

**Replica layout.** A moment operator lives on `R` replicas (later `R = Fin 4`) of one copy
`(κ → ι) × ρ` (three sites and the qubit).  A multi-replica index is `X : R → (κ → ι) × ρ`
(replica-major, as in `rearr` of L5), and for `v : R → (κ → ι) × ρ → ℂ` the moment is
`moment v = |⊗_k v_k⟩⟨⊗_k v_k|` (`prodVec` of L4).  The verifier's moments are
`Y31 = moment ![a, a, a, b]`, `Y22 = moment ![a, a, b, b]`, `Y13 = moment ![b, b, b, a]`.

**Permutation operators.** For a site diagram `w : κ → Perm R` and a qubit permutation
`wq : Perm R`, `permOp ι ρ w wq` is `⊗_i P_{w_i} ⊗ P_{wq}`: output replica `k` takes the digit of
site `i` from replica `w i k` and the qubit digit from replica `wq k` (`permIdx`).
`trace_permOp_moment`: `Tr[P_w · moment v] = wordVal w wq v = ∑_X conj(V X) V(permIdx X)`.
Every row of the verifier is a combination of such traces.

**Row families** (each holds on lifted moments, i.e. under the lift properties of L2):
* (a) `slotTrace_qpermOp`: the partial trace of a qubit permutation operator over slot `r`:
  `|ρ| · Tr_r P_p = c · Tr_r P_{p'}` with `p' = removeSlot p r` (`remove_slot` of the verifier:
  `r` deleted from its cycle) and `c = |ρ|` if `p r = r`, else `1`.
* (b) `contrast_row`: if every site permutation fixes slot `r` and `Tr_H |v_r⟩⟨v_r| = I/2`
  (and `|ρ| = 2`), then `2 Tr[P_w Y] = c Tr[P_{w'} Y]` with `w' = (w, removeSlot wq r)`,
  `c = 2` if `wq r = r` else `1`.
* (c) `row_31_22` (slot 2 fixed: `Tr[P_w Y31] = Tr[P_w Y22]`) and `row_22_13` (slot 1 fixed:
  `Tr[P_w Y22] = Tr[P_{π w π⁻¹} Y13]`, `π = (3,1,0,2)`).  **Both** need `‖a‖ = ‖b‖` (`≠ 0`):
  in 22–13 the fixed slot carries `a` in `Y22` and `b` in `Y13`.
  The general tools are `wordVal_mul_nsqC_of_fixed` (a slot fixed by every permutation factors
  out as its squared norm) and `wordVal_relabel` (relabelling replicas conjugates the diagram).
* (d) `trace_Y31`: `Tr Y31 = ‖a‖⁶‖b‖² = 1`, and `wordVal_one` (the identity word).

`removeSlot_inv` shows `remove_slot` commutes with inversion, so the rows hold whichever of the
two conventions (`P_p` or `P_{p⁻¹}`) the verifier's diagram tuples use.
-/

open Matrix

noncomputable section

namespace WernerEndpoint

section Words

variable {R κ ι ρ : Type*} [Fintype R] [DecidableEq R] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-- The index map of `⊗_i P_{w_i} ⊗ P_{wq}`. -/
def permIdx (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (X : R → (κ → ι) × ρ) :
    R → (κ → ι) × ρ :=
  fun k => (fun i => (X (w i k)).1 i, (X (wq k)).2)

variable (ι ρ) in
/-- The permutation operator `⊗_i P_{w_i} ⊗ P_{wq}` on `R` replicas of `(κ → ι) × ρ`:
`(permOp ι ρ w wq *ᵥ V) X = V (permIdx w wq X)`. -/
def permOp (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) :
    Matrix (R → (κ → ι) × ρ) (R → (κ → ι) × ρ) ℂ :=
  Matrix.of fun X Y => if Y = permIdx w wq X then 1 else 0

/-- The moment `|⊗_k v_k⟩⟨⊗_k v_k|`. -/
def moment (v : R → (κ → ι) × ρ → ℂ) : Matrix (R → (κ → ι) × ρ) (R → (κ → ι) × ρ) ℂ :=
  vecMulVec (prodVec v) (star (prodVec v))

/-- `Tr[P_w · moment v] = ⟨⊗v | P_w | ⊗v⟩`. -/
def wordVal (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (v : R → (κ → ι) × ρ → ℂ) : ℂ :=
  ∑ X, star (prodVec v X) * prodVec v (permIdx w wq X)

theorem permOp_mulVec (w : κ → Equiv.Perm R) (wq : Equiv.Perm R)
    (V : (R → (κ → ι) × ρ) → ℂ) : permOp ι ρ w wq *ᵥ V = fun X => V (permIdx w wq X) := by
  funext X
  simp [permOp, Matrix.mulVec, dotProduct]

theorem trace_permOp_moment (w : κ → Equiv.Perm R) (wq : Equiv.Perm R)
    (v : R → (κ → ι) × ρ → ℂ) : (permOp ι ρ w wq * moment v).trace = wordVal w wq v := by
  rw [moment, trace_mul_vecMulVec_star, permOp_mulVec]
  rfl

theorem summand_eq (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (v : R → (κ → ι) × ρ → ℂ)
    (X : R → (κ → ι) × ρ) :
    star (prodVec v X) * prodVec v (permIdx w wq X) =
      ∏ k, star (v k (X k)) * v k (permIdx w wq X k) := by
  simp only [prodVec, star_prod, Finset.prod_mul_distrib]

/-! ### `remove_slot` -/

/-- `removeSlot p r` deletes `r` from its cycle of `p` (the verifier's `remove_slot`):
`removeSlot p r = swap r (p r) * p`. -/
def removeSlot (p : Equiv.Perm R) (r : R) : Equiv.Perm R := Equiv.swap r (p r) * p

theorem removeSlot_apply (p : Equiv.Perm R) (r k : R) :
    removeSlot p r k = if k = r then r else if p k = r then p r else p k := by
  simp only [removeSlot, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hk : k = r
  · subst hk
    by_cases h : p k = k <;> simp [h]
  · have hne : p k ≠ p r := fun h => hk (p.injective h)
    by_cases h2 : p k = r <;> simp [hk, h2, hne]

theorem removeSlot_apply_self (p : Equiv.Perm R) (r : R) : removeSlot p r r = r := by
  simp [removeSlot_apply]

theorem removeSlot_of_fixed {p : Equiv.Perm R} {r : R} (h : p r = r) : removeSlot p r = p := by
  ext k
  rw [removeSlot_apply]
  by_cases hk : k = r
  · subst hk
    simp [h]
  · have hpk : p k ≠ r := fun h2 => hk (p.injective (h2.trans h.symm))
    simp [hk, hpk]

/-- `remove_slot` commutes with inversion. -/
theorem removeSlot_inv (p : Equiv.Perm R) (r : R) : (removeSlot p r)⁻¹ = removeSlot p⁻¹ r := by
  refine inv_eq_of_mul_eq_one_left (Equiv.ext fun k => ?_)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, removeSlot_apply p r k]
  by_cases hk : k = r
  · rw [if_pos hk, removeSlot_apply_self, hk]
  · rw [if_neg hk]
    by_cases h2 : p k = r
    · have hpr : p r ≠ r := fun h => hk (p.injective (h2.trans h.symm))
      rw [if_pos h2, removeSlot_apply, if_neg hpr, Equiv.Perm.inv_apply_self,
        if_pos (rfl : r = r), ← h2, Equiv.Perm.inv_apply_self]
    · rw [if_neg h2, removeSlot_apply, if_neg h2, Equiv.Perm.inv_apply_self, if_neg hk]

/-! ### (d) the trace row -/

theorem permIdx_one (X : R → (κ → ι) × ρ) :
    permIdx (fun _ : κ => (1 : Equiv.Perm R)) 1 X = X := by
  funext k
  simp [permIdx]

/-- The identity word: `Tr[moment v] = ∏_k ‖v_k‖²`. -/
theorem wordVal_one (v : R → (κ → ι) × ρ → ℂ) :
    wordVal (fun _ : κ => (1 : Equiv.Perm R)) 1 v = ∏ k, nsqC (v k) := by
  simp only [wordVal, permIdx_one, nsqC]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  simp only [prodVec, star_prod, Finset.prod_mul_distrib]

theorem trace_moment (v : R → (κ → ι) × ρ → ℂ) : (moment v).trace = ∏ k, nsqC (v k) := by
  rw [← wordVal_one v]
  simp only [Matrix.trace, Matrix.diag_apply, moment, Matrix.vecMulVec_apply, Pi.star_apply,
    wordVal, permIdx_one]
  exact Finset.sum_congr rfl fun X _ => mul_comm _ _

/-! ### A slot fixed by every permutation factors out -/

/-- The factors of `wordVal` away from slot `r`. -/
def fixedRest (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (r : R) (v : R → (κ → ι) × ρ → ℂ)
    (X : R → (κ → ι) × ρ) : ℂ :=
  ∏ k ∈ Finset.univ.erase r, star (v k (X k)) * v k (permIdx w wq X k)

theorem fixed_summand {w : κ → Equiv.Perm R} {wq : Equiv.Perm R} {r : R}
    (hw : ∀ i, w i r = r) (hq : wq r = r) (v : R → (κ → ι) × ρ → ℂ) (X : R → (κ → ι) × ρ)
    (y : (κ → ι) × ρ) :
    star (prodVec v (Function.update X r y)) * prodVec v (permIdx w wq (Function.update X r y)) =
      star (v r y) * v r y * fixedRest w wq r v X := by
  rw [summand_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  congr 1
  · have h1 : permIdx w wq (Function.update X r y) r = y := by
      simp [permIdx, Function.update_apply, hw, hq]
    rw [h1]
    simp
  · unfold fixedRest
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ r := Finset.ne_of_mem_erase hk
    have hne : ∀ i, w i k ≠ r := fun i h' => hk' ((w i).injective (h'.trans (hw i).symm))
    have hqk : wq k ≠ r := fun h' => hk' (wq.injective (h'.trans hq.symm))
    simp [permIdx, Function.update_apply, hne, hqk, hk']

/-- **Fixed slot.** If every site permutation and the qubit permutation fix slot `r`, and `v`,
`v'` agree away from `r`, then `wordVal v · ‖v'_r‖² = wordVal v' · ‖v_r‖²`. -/
theorem wordVal_mul_nsqC_of_fixed (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (r : R)
    (hw : ∀ i, w i r = r) (hq : wq r = r) (v v' : R → (κ → ι) × ρ → ℂ)
    (hv : ∀ k, k ≠ r → v' k = v k) :
    wordVal w wq v * nsqC (v' r) = wordVal w wq v' * nsqC (v r) := by
  have hrest : fixedRest w wq r v' = fixedRest w wq r v := by
    funext X
    unfold fixedRest
    exact Finset.prod_congr rfl fun k hk => by rw [hv k (Finset.ne_of_mem_erase hk)]
  have key : ∀ u : R → (κ → ι) × ρ → ℂ, (Fintype.card ((κ → ι) × ρ) : ℂ) * wordVal w wq u =
      nsqC (u r) * ∑ X, fixedRest w wq r u X := by
    intro u
    rw [wordVal, ← sum_sum_update _ r, Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [nsqC, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => fixed_summand hw hq u X y
  by_cases hY : (Fintype.card ((κ → ι) × ρ) : ℂ) = 0
  · simp only [nsqC, sum_eq_zero_of_card _ hY, mul_zero]
  · apply mul_left_cancel₀ hY
    rw [← mul_assoc, ← mul_assoc, key v, key v', hrest]
    ring

theorem wordVal_eq_of_fixed (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (r : R)
    (hw : ∀ i, w i r = r) (hq : wq r = r) (v v' : R → (κ → ι) × ρ → ℂ)
    (hv : ∀ k, k ≠ r → v' k = v k) (hn : nsqC (v r) = nsqC (v' r)) (hn0 : nsqC (v r) ≠ 0) :
    wordVal w wq v = wordVal w wq v' := by
  have h := wordVal_mul_nsqC_of_fixed w wq r hw hq v v' hv
  rw [← hn] at h
  exact mul_right_cancel₀ hn0 h

/-- **Relabelling replicas** conjugates the diagram. -/
theorem wordVal_relabel (τ : Equiv.Perm R) (w : κ → Equiv.Perm R) (wq : Equiv.Perm R)
    (v : R → (κ → ι) × ρ → ℂ) :
    wordVal (fun i => τ⁻¹ * w i * τ) (τ⁻¹ * wq * τ) (fun k => v (τ k)) = wordVal w wq v := by
  let e : (R → (κ → ι) × ρ) ≃ (R → (κ → ι) × ρ) :=
    { toFun := fun X => X ∘ τ
      invFun := fun X => X ∘ τ.symm
      left_inv := fun X => by funext k; simp
      right_inv := fun X => by funext k; simp }
  have hp : ∀ X : R → (κ → ι) × ρ, prodVec (fun k => v (τ k)) (X ∘ τ) = prodVec v X := by
    intro X
    simp only [prodVec, Function.comp_apply]
    exact Equiv.prod_comp τ (fun k => v k (X k))
  have hP : ∀ X : R → (κ → ι) × ρ,
      permIdx (fun i => τ⁻¹ * w i * τ) (τ⁻¹ * wq * τ) (X ∘ τ) = permIdx w wq X ∘ τ := by
    intro X
    funext k
    simp [permIdx, Equiv.Perm.mul_apply]
  unfold wordVal
  refine (Equiv.sum_comp e _).symm.trans (Finset.sum_congr rfl fun X _ => ?_)
  show star (prodVec (fun k => v (τ k)) (X ∘ τ)) *
      prodVec (fun k => v (τ k)) (permIdx (fun i => τ⁻¹ * w i * τ) (τ⁻¹ * wq * τ) (X ∘ τ)) =
    star (prodVec v X) * prodVec v (permIdx w wq X)
  rw [hP, hp, hp]

/-! ### (b) contrast rows -/

/-- The factors of `wordVal` away from slot `r` after the `H`-digits of slot `r` are summed. -/
def contrastRest (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (r : R)
    (v : R → (κ → ι) × ρ → ℂ) (X : R → (κ → ι) × ρ) (s : ρ) : ℂ :=
  ∏ k ∈ Finset.univ.erase r,
    star (v k (X k)) * v k (fun i => (X (w i k)).1 i, if wq k = r then s else (X (wq k)).2)

theorem contrast_summand {w : κ → Equiv.Perm R} {wq : Equiv.Perm R} {r : R}
    (hw : ∀ i, w i r = r) (hq : wq r ≠ r) (v : R → (κ → ι) × ρ → ℂ) (X : R → (κ → ι) × ρ)
    (h : κ → ι) (s : ρ) :
    star (prodVec v (Function.update X r (h, s))) *
        prodVec v (permIdx w wq (Function.update X r (h, s))) =
      star (v r (h, s)) * v r (h, (X (wq r)).2) * contrastRest w wq r v X s := by
  rw [summand_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  congr 1
  · have h1 : permIdx w wq (Function.update X r (h, s)) r = (h, (X (wq r)).2) := by
      simp [permIdx, hw, Function.update_apply, hq]
    rw [h1]
    simp
  · unfold contrastRest
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ r := Finset.ne_of_mem_erase hk
    have hne : ∀ i, w i k ≠ r := fun i h' => hk' ((w i).injective (h'.trans (hw i).symm))
    by_cases hk2 : wq k = r <;> simp [permIdx, Function.update_apply, hne, hk', hk2]

theorem contrast_summand' {w : κ → Equiv.Perm R} {wq : Equiv.Perm R} {r : R}
    (hw : ∀ i, w i r = r) (hq : wq r ≠ r) (v : R → (κ → ι) × ρ → ℂ) (X : R → (κ → ι) × ρ)
    (h : κ → ι) (s : ρ) :
    star (prodVec v (Function.update X r (h, s))) *
        prodVec v (permIdx w (removeSlot wq r) (Function.update X r (h, s))) =
      star (v r (h, s)) * v r (h, s) * contrastRest w wq r v X (X (wq r)).2 := by
  rw [summand_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  congr 1
  · have h1 : permIdx w (removeSlot wq r) (Function.update X r (h, s)) r = (h, s) := by
      simp [permIdx, Function.update_apply, hw, removeSlot_apply_self]
    rw [h1]
    simp
  · unfold contrastRest
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ r := Finset.ne_of_mem_erase hk
    have hne : ∀ i, w i k ≠ r := fun i h' => hk' ((w i).injective (h'.trans (hw i).symm))
    by_cases hk2 : wq k = r <;>
      simp [permIdx, Function.update_apply, hne, hk', hk2, removeSlot_apply, hq]

/-- **(b) Contrast rows.** If every site permutation fixes slot `r` and the slot-`r` vector has
qubit marginal `Tr_H |v_r⟩⟨v_r| = I/2` (with a qubit, `|ρ| = 2`), then
`2 Tr[P_{(w, wq)} Y] = c · Tr[P_{(w, removeSlot wq r)} Y]`, `c = 2` if `wq r = r`, else `1`. -/
theorem contrast_row (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (r : R) (hw : ∀ i, w i r = r)
    (v : R → (κ → ι) × ρ → ℂ)
    (hmarg : ∀ s s', ∑ h, v r (h, s) * star (v r (h, s')) = if s = s' then (1 / 2 : ℂ) else 0)
    (hρ : Fintype.card ρ = 2) :
    2 * wordVal w wq v = (if wq r = r then 2 else 1) * wordVal w (removeSlot wq r) v := by
  by_cases hq : wq r = r
  · rw [if_pos hq, removeSlot_of_fixed hq]
  rw [if_neg hq, one_mul]
  have hmarg' : ∀ s s', ∑ h, star (v r (h, s)) * v r (h, s') = if s' = s then (1 / 2 : ℂ) else 0 := by
    intro s s'
    rw [← hmarg s' s]
    exact Finset.sum_congr rfl fun h _ => mul_comm _ _
  have hY : (Fintype.card ((κ → ι) × ρ) : ℂ) ≠ 0 := by
    intro h0
    obtain ⟨s⟩ : Nonempty ρ := Fintype.card_pos_iff.mp (by omega)
    have hc : Fintype.card ((κ → ι) × ρ) = 0 := by exact_mod_cast h0
    haveI : IsEmpty ((κ → ι) × ρ) := Fintype.card_eq_zero_iff.mp hc
    haveI : IsEmpty (κ → ι) := ⟨fun h => IsEmpty.false (h, s)⟩
    have := hmarg s s
    norm_num [Finset.univ_eq_empty] at this
  have inner1 : ∀ X, ∑ y, star (prodVec v (Function.update X r y)) *
      prodVec v (permIdx w wq (Function.update X r y)) =
        1 / 2 * contrastRest w wq r v X (X (wq r)).2 := by
    intro X
    rw [Fintype.sum_prod_type]
    simp only [contrast_summand hw hq v X]
    rw [Finset.sum_comm]
    have hs : ∀ s, ∑ h, star (v r (h, s)) * v r (h, (X (wq r)).2) * contrastRest w wq r v X s =
        (if (X (wq r)).2 = s then (1 / 2 : ℂ) else 0) * contrastRest w wq r v X s := by
      intro s
      rw [← Finset.sum_mul, hmarg']
    rw [Finset.sum_congr rfl fun s _ => hs s]
    simp [ite_mul]
  have inner2 : ∀ X, ∑ y, star (prodVec v (Function.update X r y)) *
      prodVec v (permIdx w (removeSlot wq r) (Function.update X r y)) =
        contrastRest w wq r v X (X (wq r)).2 := by
    intro X
    rw [Fintype.sum_prod_type]
    simp only [contrast_summand' hw hq v X]
    rw [Finset.sum_comm]
    have h2 : ∑ s, ∑ h, star (v r (h, s)) * v r (h, s) * contrastRest w wq r v X (X (wq r)).2 =
        (∑ s, ∑ h, star (v r (h, s)) * v r (h, s)) * contrastRest w wq r v X (X (wq r)).2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by rw [Finset.sum_mul]
    have h3 : ∑ s : ρ, ∑ h, star (v r (h, s)) * v r (h, s) = 1 := by
      rw [Finset.sum_congr rfl fun s _ => hmarg' s s]
      norm_num [hρ]
    rw [h2, h3, one_mul]
  have e1 : (Fintype.card ((κ → ι) × ρ) : ℂ) * wordVal w wq v =
      ∑ X, 1 / 2 * contrastRest w wq r v X (X (wq r)).2 := by
    rw [wordVal, ← sum_sum_update _ r]
    exact Finset.sum_congr rfl fun X _ => inner1 X
  have e2 : (Fintype.card ((κ → ι) × ρ) : ℂ) * wordVal w (removeSlot wq r) v =
      ∑ X, contrastRest w wq r v X (X (wq r)).2 := by
    rw [wordVal, ← sum_sum_update _ r]
    exact Finset.sum_congr rfl fun X _ => inner2 X
  apply mul_left_cancel₀ hY
  rw [mul_left_comm, e1, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  ring

end Words

/-! ### (a) qubit partial trace of a permutation operator -/

section Qubit

variable {R ρ : Type*} [Fintype R] [DecidableEq R] [Fintype ρ] [DecidableEq ρ]

variable (R ρ) in
/-- The qubit permutation operator `P_p` on `ρ^{⊗R}`: `(P_p v)(s) = v (s ∘ p)`. -/
def qpermOp (p : Equiv.Perm R) : Matrix (R → ρ) (R → ρ) ℂ :=
  Matrix.of fun s t => if t = s ∘ p then 1 else 0

/-- The partial trace over slot `r`, kept on the full index (the result does not depend on the
slot-`r` digits): `(slotTrace r M) s t = ∑_y M (s[r ↦ y]) (t[r ↦ y])`. -/
def slotTrace (r : R) (M : Matrix (R → ρ) (R → ρ) ℂ) : Matrix (R → ρ) (R → ρ) ℂ :=
  Matrix.of fun s t => ∑ y, M (Function.update s r y) (Function.update t r y)

/-- **(a)** `|ρ| · Tr_r P_p = c · Tr_r P_{removeSlot p r}`, `c = |ρ|` if `p r = r`, else `1`
(for a qubit: `Tr_r P_p = P_{p'}` on the other slots when `p` moves `r`). -/
theorem slotTrace_qpermOp (p : Equiv.Perm R) (r : R) :
    (Fintype.card ρ : ℂ) • slotTrace r (qpermOp R ρ p) =
      (if p r = r then (Fintype.card ρ : ℂ) else 1) • slotTrace r (qpermOp R ρ (removeSlot p r)) := by
  classical
  by_cases hp : p r = r
  · rw [if_pos hp, removeSlot_of_fixed hp]
  rw [if_neg hp, one_smul]
  have hne : ∀ k, k ≠ r → removeSlot p r k ≠ r := fun k hk h =>
    hk ((removeSlot p r).injective (h.trans (removeSlot_apply_self p r).symm))
  ext s t
  simp only [Matrix.smul_apply, slotTrace, qpermOp, Matrix.of_apply, smul_eq_mul]
  have hΦ' : ∀ y, (Function.update t r y = Function.update s r y ∘ removeSlot p r) ↔
      (∀ k, k ≠ r → t k = s (removeSlot p r k)) := by
    intro y
    rw [funext_iff]
    constructor
    · intro h k hk
      have h1 := h k
      simpa [Function.update_apply, hk, hne k hk] using h1
    · intro h k
      by_cases hk : k = r
      · subst hk
        simp [Function.update_apply, removeSlot_apply_self]
      · simpa [Function.update_apply, hk, hne k hk] using h k hk
  have hΦ : ∀ y, (Function.update t r y = Function.update s r y ∘ p) ↔
      (y = s (p r) ∧ ∀ k, k ≠ r → t k = s (removeSlot p r k)) := by
    intro y
    rw [funext_iff]
    constructor
    · intro h
      have hyr : y = s (p r) := by simpa [Function.update_apply, hp] using h r
      refine ⟨hyr, fun k hk => ?_⟩
      have h1 := h k
      rw [removeSlot_apply, if_neg hk]
      by_cases h2 : p k = r
      · rw [if_pos h2]
        simp [Function.update_apply, hk, h2] at h1
        rw [h1, hyr]
      · rw [if_neg h2]
        simpa [Function.update_apply, hk, h2] using h1
    · rintro ⟨hyr, hΦk⟩ k
      by_cases hk : k = r
      · subst hk
        simp [Function.update_apply, hp, hyr]
      · have h1 := hΦk k hk
        rw [removeSlot_apply, if_neg hk] at h1
        simp only [Function.comp_apply, Function.update_apply, if_neg hk]
        by_cases h2 : p k = r
        · rw [if_pos h2] at h1
          rw [if_pos h2, h1, hyr]
        · rw [if_neg h2] at h1
          rw [if_neg h2, h1]
  simp only [hΦ, hΦ', ite_and]
  rw [Finset.sum_ite_eq']
  simp

end Qubit

/-! ### (c) marginal rows and (d) the trace row on the four-replica moments -/

section Rows

variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ]

/-- `π = (3, 1, 0, 2)` (`PI_ABB` of the verifier), as a permutation `j ↦ π[j]` of `Fin 4`. -/
def piABB : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

/-- **(c) 31–22 rows.** If every permutation fixes slot 2 and `‖a‖ = ‖b‖ ≠ 0`,
`Tr[P_w Y31] = Tr[P_w Y22]`. -/
theorem row_31_22 (a b : (κ → ι) × ρ → ℂ) (hab : nsqC a = nsqC b) (ha0 : nsqC a ≠ 0)
    (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) (hw : ∀ i, w i 2 = 2) (hq : wq 2 = 2) :
    wordVal w wq ![a, a, a, b] = wordVal w wq ![a, a, b, b] := by
  refine wordVal_eq_of_fixed w wq 2 hw hq _ _ ?_ hab ha0
  intro k hk
  fin_cases k
  · rfl
  · rfl
  · exact absurd rfl hk
  · rfl

/-- **(c) 22–13 rows.** If every permutation fixes slot 1 and `‖a‖ = ‖b‖ ≠ 0`,
`Tr[P_w Y22] = Tr[P_{π w π⁻¹} Y13]`. -/
theorem row_22_13 (a b : (κ → ι) × ρ → ℂ) (hab : nsqC a = nsqC b) (ha0 : nsqC a ≠ 0)
    (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) (hw : ∀ i, w i 1 = 1) (hq : wq 1 = 1) :
    wordVal w wq ![a, a, b, b] =
      wordVal (fun i => piABB * w i * piABB⁻¹) (piABB * wq * piABB⁻¹) ![b, b, b, a] := by
  have h1 := wordVal_relabel piABB⁻¹ w wq ![a, a, b, b]
  simp only [inv_inv] at h1
  rw [← h1]
  have hπ1 : piABB 1 = 1 := by rfl
  have hπi1 : piABB⁻¹ 1 = 1 := by rfl
  refine wordVal_eq_of_fixed _ _ 1 ?_ ?_ _ _ ?_ hab ha0
  · intro i
    simp only [Equiv.Perm.mul_apply, hπi1, hw, hπ1]
  · simp only [Equiv.Perm.mul_apply, hπi1, hq, hπ1]
  · intro k hk
    fin_cases k
    · rfl
    · exact absurd rfl hk
    · rfl
    · rfl

/-- **(d) Trace row.** `Tr Y31 = ‖a‖⁶ ‖b‖² = 1` for unit `a`, `b`. -/
theorem trace_Y31 (a b : (κ → ι) × ρ → ℂ) (ha : nsqC a = 1) (hb : nsqC b = 1) :
    (moment ![a, a, a, b]).trace = 1 := by
  rw [trace_moment, Fin.prod_univ_four]
  have e0 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 0 = a := rfl
  have e1 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 1 = a := rfl
  have e2 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 2 = a := rfl
  have e3 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 3 = b := rfl
  rw [e0, e1, e2, e3, ha, hb]
  norm_num

end Rows

end WernerEndpoint

end

#print axioms WernerEndpoint.permOp_mulVec
#print axioms WernerEndpoint.trace_permOp_moment
#print axioms WernerEndpoint.removeSlot_apply
#print axioms WernerEndpoint.removeSlot_of_fixed
#print axioms WernerEndpoint.removeSlot_inv
#print axioms WernerEndpoint.wordVal_one
#print axioms WernerEndpoint.trace_moment
#print axioms WernerEndpoint.wordVal_mul_nsqC_of_fixed
#print axioms WernerEndpoint.wordVal_eq_of_fixed
#print axioms WernerEndpoint.wordVal_relabel
#print axioms WernerEndpoint.contrast_row
#print axioms WernerEndpoint.slotTrace_qpermOp
#print axioms WernerEndpoint.row_31_22
#print axioms WernerEndpoint.row_22_13
#print axioms WernerEndpoint.trace_Y31
