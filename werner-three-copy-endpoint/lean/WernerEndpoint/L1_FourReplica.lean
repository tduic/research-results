import WernerEndpoint.L1_Swap
import WernerEndpoint.L3_Rows

/-!
# L1, four-replica form: `q(C) = Tr[W · Y31]`

The verifier's moments are four-replica moments, and its objective `c8` is
`8 c = ∑_S (-1)^{|S|} 2^{3-|S|} · (⊗_i (S03 if i ∈ S else E) ⊗ S03)` on `Y31`, where `S03` is the
transposition of replicas `0` and `3` (`E` the identity).  So the objective word is

  `objective4 = ∑_S (-1/2)^{|S|} permOp ι ρ (objSites S) (swap 0 3)`,  `objSites S i = swap 0 3`
  for `i ∈ S` and `1` otherwise.

`wordVal_objective`: on `Y31 = |a a a b⟩⟨a a a b|` the two spectator replicas `1, 2` (fixed by the
word) contribute `‖a‖⁴`, and the rest is the two-replica expectation of L1.
`qfun_eq_trace_four`: for `‖a‖ = 1`, `q(∑_r |a_r⟩⟨b_r|) = Tr[objective4 · Y31]`.
-/

open Matrix

noncomputable section

namespace WernerEndpoint

section Four

variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ]

/-- The site part of the objective word for the subset `S`. -/
def objSites (S : Finset κ) : κ → Equiv.Perm (Fin 4) :=
  fun i => if i ∈ S then Equiv.swap 0 3 else 1

variable (κ ι ρ) in
/-- The four-replica objective word `W = ∑_S (-1/2)^{|S|} ⊗_i (S03 or E) ⊗ S03` (`c8 / 8`). -/
def objective4 : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  ∑ S : Finset κ, ((-1 / 2 : ℂ) ^ S.card) • permOp ι ρ (objSites S) (Equiv.swap 0 3)

/-- `![y0, y1, y2, y3]` under a name with `rfl` evaluation lemmas. -/
def mk4 {Y : Type*} (y0 y1 y2 y3 : Y) : Fin 4 → Y := ![y0, y1, y2, y3]

theorem mk4_0 {Y : Type*} (y0 y1 y2 y3 : Y) : mk4 y0 y1 y2 y3 0 = y0 := rfl
theorem mk4_1 {Y : Type*} (y0 y1 y2 y3 : Y) : mk4 y0 y1 y2 y3 1 = y1 := rfl
theorem mk4_2 {Y : Type*} (y0 y1 y2 y3 : Y) : mk4 y0 y1 y2 y3 2 = y2 := rfl
theorem mk4_3 {Y : Type*} (y0 y1 y2 y3 : Y) : mk4 y0 y1 y2 y3 3 = y3 := rfl

theorem sum_fin4 {Y : Type*} [Fintype Y] (f : (Fin 4 → Y) → ℂ) :
    ∑ X, f X = ∑ y0, ∑ y1, ∑ y2, ∑ y3, f (mk4 y0 y1 y2 y3) := by
  let e : Y × Y × Y × Y ≃ (Fin 4 → Y) :=
    { toFun := fun p => mk4 p.1 p.2.1 p.2.2.1 p.2.2.2
      invFun := fun X => (X 0, X 1, X 2, X 3)
      left_inv := fun p => rfl
      right_inv := fun X => by
        funext i
        fin_cases i <;> rfl }
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

theorem swap03_0 : Equiv.swap (0 : Fin 4) 3 0 = 3 := Equiv.swap_apply_left _ _
theorem swap03_3 : Equiv.swap (0 : Fin 4) 3 3 = 0 := Equiv.swap_apply_right _ _
theorem swap03_1 : Equiv.swap (0 : Fin 4) 3 1 = 1 := by
  rfl
theorem swap03_2 : Equiv.swap (0 : Fin 4) 3 2 = 2 := by
  rfl

theorem permIdx_obj_0 (S : Finset κ) (X : Fin 4 → (κ → ι) × ρ) :
    permIdx (objSites S) (Equiv.swap 0 3) X 0 = (swapSites S (X 0).1 (X 3).1, (X 3).2) := by
  refine Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i ∈ S <;> simp [permIdx, objSites, swapSites, hi, swap03_0]
  · simp [permIdx, swap03_0]

theorem permIdx_obj_3 (S : Finset κ) (X : Fin 4 → (κ → ι) × ρ) :
    permIdx (objSites S) (Equiv.swap 0 3) X 3 = (swapSites S (X 3).1 (X 0).1, (X 0).2) := by
  refine Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i ∈ S <;> simp [permIdx, objSites, swapSites, hi, swap03_3]
  · simp [permIdx, swap03_3]

theorem permIdx_obj_1 (S : Finset κ) (X : Fin 4 → (κ → ι) × ρ) :
    permIdx (objSites S) (Equiv.swap 0 3) X 1 = X 1 := by
  refine Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i ∈ S <;> simp [permIdx, objSites, hi, swap03_1]
  · simp [permIdx, swap03_1]

theorem permIdx_obj_2 (S : Finset κ) (X : Fin 4 → (κ → ι) × ρ) :
    permIdx (objSites S) (Equiv.swap 0 3) X 2 = X 2 := by
  refine Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i ∈ S <;> simp [permIdx, objSites, hi, swap03_2]
  · simp [permIdx, swap03_2]

theorem sum4_factor {Y : Type*} [Fintype Y] (A B : Y → ℂ) (T : Y → Y → ℂ) :
    ∑ y0, ∑ y1, ∑ y2, ∑ y3, A y1 * B y2 * T y0 y3 =
      (∑ y, A y) * (∑ y, B y) * ∑ y0, ∑ y3, T y0 y3 := by
  calc ∑ y0, ∑ y1, ∑ y2, ∑ y3, A y1 * B y2 * T y0 y3
      = ∑ y1, ∑ y0, ∑ y2, ∑ y3, A y1 * B y2 * T y0 y3 := Finset.sum_comm
    _ = ∑ y1, ∑ y2, ∑ y0, ∑ y3, A y1 * B y2 * T y0 y3 :=
        Finset.sum_congr rfl fun y1 _ => Finset.sum_comm
    _ = (∑ y, A y) * (∑ y, B y) * ∑ y0, ∑ y3, T y0 y3 := by
        rw [mul_sum_sum]
        simp only [Finset.sum_mul]
        simp only [Finset.mul_sum]

/-- On `Y31 = |a a a b⟩⟨a a a b|` the objective word for `S` is `‖a‖⁴ ⟨a⊗b|F_Q ∏_{i∈S} F_i|a⊗b⟩`. -/
theorem wordVal_objective (S : Finset κ) (a b : (κ → ι) × ρ → ℂ) :
    wordVal (objSites S) (Equiv.swap 0 3) ![a, a, a, b] =
      nsqC a * nsqC a * (star (twoRep a b) ⬝ᵥ (swapOp ι ρ S *ᵥ twoRep a b)) := by
  have e0 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 0 = a := rfl
  have e1 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 1 = a := rfl
  have e2 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 2 = a := rfl
  have e3 : (![a, a, a, b] : Fin 4 → (κ → ι) × ρ → ℂ) 3 = b := rfl
  have key : ∀ X : Fin 4 → (κ → ι) × ρ,
      star (prodVec ![a, a, a, b] X) * prodVec ![a, a, a, b] (permIdx (objSites S) (Equiv.swap 0 3) X) =
        star (a (X 1)) * a (X 1) * (star (a (X 2)) * a (X 2)) *
          (star (twoRep a b (X 0, X 3)) * twoRep a b (swapIdx S (X 0, X 3))) := by
    intro X
    rw [summand_eq, Fin.prod_univ_four, e0, e1, e2, e3, permIdx_obj_0, permIdx_obj_1,
      permIdx_obj_2, permIdx_obj_3]
    simp only [twoRep, swapIdx, star_mul']
    ring
  rw [wordVal, sum_fin4]
  simp only [key, mk4_0, mk4_1, mk4_2, mk4_3]
  refine (sum4_factor _ _ _).trans ?_
  rw [swapOp_mulVec]
  simp only [nsqC, dotProduct, Pi.star_apply, Fintype.sum_prod_type]

/-- **L1 (four-replica objective).** For `‖a‖ = 1`,
`q(∑_r |a_r⟩⟨b_r|) = Tr[objective4 · Y31]`, `Y31 = |a a a b⟩⟨a a a b|`. -/
theorem qfun_eq_trace_four (a b : (κ → ι) × ρ → ℂ) (ha : nsqC a = 1) :
    ((qfun (liftC a b) : ℝ) : ℂ) = (objective4 κ ι ρ * moment ![a, a, a, b]).trace := by
  rw [objective4, Finset.sum_mul, Matrix.trace_sum, qfun, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_permOp_moment, wordVal_objective,
    ← frobSq_partialTrace_liftC, smul_eq_mul]
  simp only [ha, one_mul]
  push_cast; ring

end Four

end WernerEndpoint

end

#print axioms WernerEndpoint.sum_fin4
#print axioms WernerEndpoint.sum4_factor
#print axioms WernerEndpoint.wordVal_objective
#print axioms WernerEndpoint.qfun_eq_trace_four
