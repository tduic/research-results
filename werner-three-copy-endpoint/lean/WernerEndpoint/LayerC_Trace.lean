import WernerEndpoint.L3_Rows
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Layer C: the trace formula for permutation operators

`verify_d5.py` (C) evaluates every objective and row coefficient with

  `Tr[⊗_i P_{w_i} ⊗ P_{wq} · ⊗_i P_{t_i} ⊗ P_{tq}] = ∏_i d^{cyc(w_i t_i)} · 2^{cyc(wq tq)}`,

where `cyc` counts **all** cycles, fixed points included (Mathlib's `cycleType` omits 1-cycles).

* `permOp_mul`: `P_{(w,wq)} P_{(t,tq)} = P_{(w t, wq tq)}` (pointwise products; `(w i * t i) k =
  w i (t i k)`), so the diagram of a product is the verifier's `comp(w, t)`.
* `permOp_one`, `permOp_conjTranspose`: `P_1 = 1`, `P_wᴴ = P_{w⁻¹}`.
* `fixCount ι p = #{f : R → ι | f ∘ p = f}` and `trace_permOp`:
  `Tr P_{(u,uq)} = ∏_i fixCount ι (u i) · fixCount ρ uq`.
* `cycCount p` = the number of classes of `SameCycle p` (all cycles, fixed points included), and
  `fixCount_eq_pow`: `fixCount ι p = |ι| ^ cycCount p`.
* **Trace formula** `trace_permOp_mul_permOp`:
  `Tr[P_{(w,wq)} P_{(t,tq)}] = ∏_i |ι|^{cycCount (w i * t i)} · |ρ|^{cycCount (wq * tq)}`.
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Trace

variable {R κ ι ρ : Type*} [Fintype R] [DecidableEq R] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

theorem permIdx_permIdx (w t : κ → Equiv.Perm R) (wq tq : Equiv.Perm R) (X : R → (κ → ι) × ρ) :
    permIdx t tq (permIdx w wq X) = permIdx (fun i => w i * t i) (wq * tq) X :=
  rfl

/-- `P_{(w,wq)} P_{(t,tq)} = P_{(w t, wq tq)}`. -/
theorem permOp_mul (w t : κ → Equiv.Perm R) (wq tq : Equiv.Perm R) :
    permOp ι ρ w wq * permOp ι ρ t tq = permOp ι ρ (fun i => w i * t i) (wq * tq) := by
  ext X Z
  simp only [permOp, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem permIdx_one' (X : R → (κ → ι) × ρ) :
    permIdx (fun _ : κ => (1 : Equiv.Perm R)) 1 X = X := rfl

/-- `P_1 = 1`. -/
theorem permOp_one : permOp ι ρ (fun _ : κ => (1 : Equiv.Perm R)) 1 = 1 := by
  ext X Y
  simp only [permOp, Matrix.of_apply, Matrix.one_apply, permIdx_one']
  by_cases h : X = Y
  · subst h; simp
  · simp [h, Ne.symm h]

theorem permIdx_inv (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (X : R → (κ → ι) × ρ) :
    permIdx (fun i => (w i)⁻¹) wq⁻¹ (permIdx w wq X) = X := by
  funext k
  refine Prod.ext (funext fun i => ?_) ?_
  · show (X (w i ((w i)⁻¹ k))).1 i = (X k).1 i
    rw [Equiv.Perm.apply_inv_self]
  · show (X (wq (wq⁻¹ k))).2 = (X k).2
    rw [Equiv.Perm.apply_inv_self]

theorem permIdx_inv' (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) (X : R → (κ → ι) × ρ) :
    permIdx w wq (permIdx (fun i => (w i)⁻¹) wq⁻¹ X) = X := by
  funext k
  refine Prod.ext (funext fun i => ?_) ?_
  · show (X ((w i)⁻¹ (w i k))).1 i = (X k).1 i
    rw [Equiv.Perm.inv_apply_self]
  · show (X (wq⁻¹ (wq k))).2 = (X k).2
    rw [Equiv.Perm.inv_apply_self]

/-- `P_wᴴ = P_{w⁻¹}`. -/
theorem permOp_conjTranspose (w : κ → Equiv.Perm R) (wq : Equiv.Perm R) :
    (permOp ι ρ w wq)ᴴ = permOp ι ρ (fun i => (w i)⁻¹) wq⁻¹ := by
  ext X Y
  simp only [permOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (X = permIdx w wq Y) ↔ (Y = permIdx (fun i => (w i)⁻¹) wq⁻¹ X) := by
    constructor
    · rintro rfl; exact (permIdx_inv w wq Y).symm
    · rintro rfl; exact (permIdx_inv' w wq X).symm
  by_cases h : X = permIdx w wq Y
  · rw [if_pos h, if_pos (this.mp h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; simp

/-- The number of `ι`-colourings of `R` invariant under `p`. -/
def fixCount (ι : Type*) [Fintype ι] [DecidableEq ι] (p : Equiv.Perm R) : ℕ :=
  Fintype.card {f : R → ι // f ∘ p = f}

theorem permIdx_eq_self_iff (u : κ → Equiv.Perm R) (uq : Equiv.Perm R) (X : R → (κ → ι) × ρ) :
    permIdx u uq X = X ↔
      (∀ i, (fun k => (X k).1 i) ∘ u i = fun k => (X k).1 i) ∧
        (fun k => (X k).2) ∘ uq = fun k => (X k).2 := by
  constructor
  · intro h
    refine ⟨fun i => funext fun k => ?_, funext fun k => ?_⟩
    · exact congrArg (fun Y : R → (κ → ι) × ρ => (Y k).1 i) h
    · exact congrArg (fun Y : R → (κ → ι) × ρ => (Y k).2) h
  · rintro ⟨h1, h2⟩
    funext k
    refine Prod.ext (funext fun i => ?_) ?_
    · exact congrFun (h1 i) k
    · exact congrFun h2 k

/-- Replica-major multi-indices as (site colourings, qubit colouring). -/
def splitIdx : (R → (κ → ι) × ρ) ≃ (κ → R → ι) × (R → ρ) where
  toFun X := (fun i k => (X k).1 i, fun k => (X k).2)
  invFun F := fun k => (fun i => F.1 i k, F.2 k)
  left_inv X := funext fun k => Prod.ext (funext fun i => rfl) rfl
  right_inv F := Prod.ext (funext fun i => funext fun k => rfl) (funext fun k => rfl)

/-- `Tr P_{(u,uq)} = ∏_i fixCount ι (u i) · fixCount ρ uq`. -/
theorem trace_permOp (u : κ → Equiv.Perm R) (uq : Equiv.Perm R) :
    (permOp ι ρ u uq).trace = (((∏ i, fixCount ι (u i)) * fixCount ρ uq : ℕ) : ℂ) := by
  have h1 : (permOp ι ρ u uq).trace =
      ((Fintype.card {X : R → (κ → ι) × ρ // permIdx u uq X = X} : ℕ) : ℂ) := by
    rw [Fintype.card_subtype]
    simp only [Matrix.trace, Matrix.diag_apply, permOp, Matrix.of_apply]
    rw [Finset.sum_boole]
    congr 2
    ext X
    simp [eq_comm]
  rw [h1]
  congr 1
  let e : {X : R → (κ → ι) × ρ // permIdx u uq X = X} ≃
      {F : (κ → R → ι) × (R → ρ) // (∀ i, F.1 i ∘ u i = F.1 i) ∧ F.2 ∘ uq = F.2} :=
    Equiv.subtypeEquiv splitIdx fun X => permIdx_eq_self_iff u uq X
  rw [Fintype.card_congr e, Fintype.card_congr (Equiv.subtypeProdEquivProd
      (p := fun F : κ → R → ι => ∀ i, F i ∘ u i = F i) (q := fun g : R → ρ => g ∘ uq = g)),
    Fintype.card_prod, Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun (i : κ) (f : R → ι) => f ∘ u i = f)), Fintype.card_pi]
  rfl

/-- `P_{(w,wq)} P_{(t,tq)}` has trace `∏_i fixCount ι (w i t i) · fixCount ρ (wq tq)`. -/
theorem trace_permOp_mul_permOp' (w t : κ → Equiv.Perm R) (wq tq : Equiv.Perm R) :
    (permOp ι ρ w wq * permOp ι ρ t tq).trace =
      (((∏ i, fixCount ι (w i * t i)) * fixCount ρ (wq * tq) : ℕ) : ℂ) := by
  rw [permOp_mul, trace_permOp]

/-! ### Invariant colourings and cycles -/

/-- The number of cycles of `p`, fixed points included. -/
def cycCount (p : Equiv.Perm R) : ℕ := Nat.card (Quot p.SameCycle)

theorem comp_eq_of_sameCycle {β : Type*} {p : Equiv.Perm R} {f : R → β} (hf : f ∘ p = f) {a b : R}
    (h : p.SameCycle a b) : f a = f b := by
  have h1 : ∀ x, f (p x) = f x := fun x => congrFun hf x
  have h2 : ∀ n : ℕ, ∀ x, f ((p ^ n) x) = f x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
  obtain ⟨i, rfl⟩ := h
  cases i with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact (h2 n a).symm
  | negSucc n =>
    rw [zpow_negSucc]
    have := h2 (n + 1) ((p ^ (n + 1))⁻¹ a)
    rw [Equiv.Perm.apply_inv_self] at this
    exact this

/-- `p`-invariant colourings are colourings of the cycles of `p`. -/
def fixEquiv (ι : Type*) (p : Equiv.Perm R) :
    {f : R → ι // f ∘ p = f} ≃ (Quot p.SameCycle → ι) where
  toFun f := Quot.lift f.1 fun _ _ h => comp_eq_of_sameCycle f.2 h
  invFun g := ⟨g ∘ Quot.mk _, funext fun x =>
    congrArg g (Quot.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl p x)))⟩
  left_inv f := Subtype.ext rfl
  right_inv g := funext fun q => Quot.inductionOn q fun _ => rfl

/-- `fixCount ι p = |ι| ^ (number of cycles of p)`. -/
theorem fixCount_eq_pow (p : Equiv.Perm R) : fixCount ι p = Fintype.card ι ^ cycCount p := by
  rw [fixCount, ← Nat.card_eq_fintype_card, Nat.card_congr (fixEquiv ι p), Nat.card_fun,
    Nat.card_eq_fintype_card, cycCount]

/-- **Trace formula.** `Tr[P_{(w,wq)} P_{(t,tq)}] = ∏_i |ι|^{cyc(w_i t_i)} · |ρ|^{cyc(wq tq)}`,
cycles counted with fixed points. -/
theorem trace_permOp_mul_permOp (w t : κ → Equiv.Perm R) (wq tq : Equiv.Perm R) :
    (permOp ι ρ w wq * permOp ι ρ t tq).trace =
      (((∏ i, Fintype.card ι ^ cycCount (w i * t i)) *
        Fintype.card ρ ^ cycCount (wq * tq) : ℕ) : ℂ) := by
  rw [trace_permOp_mul_permOp']
  simp only [fixCount_eq_pow]

end Trace

end WernerEndpoint

end

#print axioms WernerEndpoint.permOp_mul
#print axioms WernerEndpoint.permOp_one
#print axioms WernerEndpoint.permOp_conjTranspose
#print axioms WernerEndpoint.trace_permOp
#print axioms WernerEndpoint.fixCount_eq_pow
#print axioms WernerEndpoint.trace_permOp_mul_permOp
