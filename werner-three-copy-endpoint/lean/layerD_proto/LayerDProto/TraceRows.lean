import LayerDProto.PermTables
import WernerEndpoint.LayerC_Trace
import WernerEndpoint.LayerC_WalledCore
import WernerEndpoint.L1_FourReplica

/-!
# Layer D, (E′): rows and objective as tuple functionals (trace formula, index form)

Layer C's `trace_permOp_mul_permOp` gives `Tr[P_w P_t] = ∏_i |ι|^{cyc(w_i t_i)} · |ρ|^{cyc(wq tq)}`.
Here the cycle counts and the products of the 24 permutations are replaced by the index tables of
`PermTables.lean` (`cycTab`, `mulTab`), proved equal to `cycCount` and `*` on `permTab` once:

* `permTab_mulTab`: `permTab (mulTab a b) = permTab a * permTab b`; `permTab_invTab`;
* `cycCount_permTab`: `cycCount (permTab a) = cycTab a` (via `fixCount (Fin 2) = 2 ^ cycCount`);
* `permEquiv : Fin 24 ≃ Perm (Fin 4)`, `tupEquiv` for diagram tuples;
* `trace_word_idx`: `Tr[P_{w} P_{t}] = wordNat |ι| |ρ| w t` on index tuples (a natural number);
* `trace_mul_rep`: for `M = ∑_t x_t P_t`, `Tr[P_w M] = ∑_{index tuples} x_t · wordNat w t`, which is
  how every verifier row and the objective become tuple functionals with computable coefficients;
* `trace_objective4_mul_rep`: the same for `objective4` (`c8 / 8`).
-/

open Matrix WernerEndpoint

noncomputable section

namespace LayerDProto

/-! ### The tables against `permTab` -/

theorem permFun_mulTab : ∀ a b : Fin 24, ∀ x : Fin 4, permFun (mulTab a b) x = permFun a (permFun b x) := by
  decide

theorem permTab_mulTab (a b : Fin 24) : permTab (mulTab a b) = permTab a * permTab b :=
  Equiv.ext fun x => permFun_mulTab a b x

theorem permFun_invTab : ∀ a : Fin 24, ∀ x : Fin 4, permFun (invTab a) x = permInv a x := by
  decide

theorem permTab_invTab (a : Fin 24) : permTab (invTab a) = (permTab a)⁻¹ :=
  Equiv.ext fun x => permFun_invTab a x

theorem permTab_inj : Function.Injective permTab := by
  intro a b hab
  have : ∀ k, permFun a k = permFun b k := fun k => congrArg (fun e => e k) hab
  revert this; revert a b; decide

/-- The listing `PERMS` as an equivalence. -/
def permEquiv : Fin 24 ≃ Equiv.Perm (Fin 4) :=
  Equiv.ofBijective permTab ⟨permTab_inj, permTab_surj⟩

theorem permEquiv_apply (a : Fin 24) : permEquiv a = permTab a := rfl

/-- Diagram tuples in index form. -/
def tupEquiv : (Fin 3 → Fin 24) × Fin 24 ≃ (Fin 3 → Equiv.Perm (Fin 4)) × Equiv.Perm (Fin 4) :=
  (Equiv.arrowCongr (Equiv.refl _) permEquiv).prodCongr permEquiv

theorem tupEquiv_apply (t : (Fin 3 → Fin 24) × Fin 24) :
    tupEquiv t = (fun i => permTab (t.1 i), permTab t.2) := rfl

/-! ### Cycle counts -/

theorem fixCount_two_permTab : ∀ a : Fin 24, fixCount (Fin 2) (permTab a) = 2 ^ cycTab a := by
  decide

theorem cycCount_permTab (a : Fin 24) : cycCount (permTab a) = cycTab a := by
  have h := fixCount_eq_pow (ι := Fin 2) (permTab a)
  rw [fixCount_two_permTab, Fintype.card_fin] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

/-! ### Words -/

/-- `∏_i d^{cyc(w_i t_i)} · e^{cyc(wq tq)}` on index tuples. -/
def wordNat (d e : ℕ) (w t : (Fin 3 → Fin 24) × Fin 24) : ℕ :=
  (∏ i, d ^ cycTab (mulTab (w.1 i) (t.1 i))) * e ^ cycTab (mulTab w.2 t.2)

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-- The trace formula in index form. -/
theorem trace_word_idx (w t : (Fin 3 → Fin 24) × Fin 24) :
    (permOp ι ρ (tupEquiv w).1 (tupEquiv w).2 * permOp ι ρ (tupEquiv t).1 (tupEquiv t).2).trace =
      (wordNat (Fintype.card ι) (Fintype.card ρ) w t : ℂ) := by
  rw [trace_permOp_mul_permOp]
  simp only [tupEquiv_apply, ← permTab_mulTab, cycCount_permTab, wordNat]

/-- **Rows as tuple functionals.** For `M = ∑_t x_t P_t` (e.g. `twirl_rep`),
`Tr[P_w M] = ∑_{index tuples t} x_t · wordNat |ι| |ρ| w t`. -/
theorem trace_mul_rep (x : (Fin 3 → Equiv.Perm (Fin 4)) × Equiv.Perm (Fin 4) → ℂ)
    (w : (Fin 3 → Fin 24) × Fin 24) :
    (permOp ι ρ (tupEquiv w).1 (tupEquiv w).2 * ∑ t, x t • permOp ι ρ t.1 t.2).trace =
      ∑ t : (Fin 3 → Fin 24) × Fin 24,
        x (tupEquiv t) * (wordNat (Fintype.card ι) (Fintype.card ρ) w t : ℂ) := by
  rw [Matrix.mul_sum, Matrix.trace_sum, ← Equiv.sum_comp tupEquiv]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, trace_word_idx, smul_eq_mul]

/-! ### The objective -/

/-- The index of `swap 0 3` in `PERMS` (`(3, 1, 2, 0)`). -/
def s03 : Fin 24 := 21

theorem permTab_s03 : permTab s03 = Equiv.swap 0 3 := by
  ext x; revert x; decide

theorem permTab_zero : permTab 0 = 1 := by
  ext x; revert x; decide

/-- The objective word for `S` in index form. -/
def objIdx (S : Finset (Fin 3)) : (Fin 3 → Fin 24) × Fin 24 :=
  (fun i => if i ∈ S then s03 else 0, s03)

theorem tupEquiv_objIdx (S : Finset (Fin 3)) :
    tupEquiv (objIdx S) = (objSites S, Equiv.swap 0 3) := by
  rw [tupEquiv_apply]
  refine Prod.ext (funext fun i => ?_) permTab_s03
  simp only [objIdx, objSites]
  split_ifs
  · exact permTab_s03
  · exact permTab_zero

/-- The objective as a tuple functional: `∑_S (-1/2)^{|S|} wordNat (objIdx S) t` (`c8 / 8`). -/
def objFun (d e : ℕ) (t : (Fin 3 → Fin 24) × Fin 24) : ℂ :=
  ∑ S : Finset (Fin 3), (-1 / 2 : ℂ) ^ S.card * (wordNat d e (objIdx S) t : ℂ)

theorem trace_objective4_mul_rep (x : (Fin 3 → Equiv.Perm (Fin 4)) × Equiv.Perm (Fin 4) → ℂ) :
    (objective4 (Fin 3) ι ρ * ∑ t, x t • permOp ι ρ t.1 t.2).trace =
      ∑ t : (Fin 3 → Fin 24) × Fin 24, x (tupEquiv t) * objFun (Fintype.card ι) (Fintype.card ρ) t := by
  set M := ∑ t, x t • permOp ι ρ t.1 t.2 with hM
  have h : ∀ S : Finset (Fin 3),
      (((-1 / 2 : ℂ) ^ S.card) • permOp ι ρ (objSites S) (Equiv.swap 0 3) * M).trace =
        ∑ t : (Fin 3 → Fin 24) × Fin 24, x (tupEquiv t) *
          ((-1 / 2 : ℂ) ^ S.card * (wordNat (Fintype.card ι) (Fintype.card ρ) (objIdx S) t : ℂ)) := by
    intro S
    have e := trace_mul_rep (ι := ι) (ρ := ρ) x (objIdx S)
    rw [tupEquiv_objIdx] at e
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hM, e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [objective4, Finset.sum_mul, Matrix.trace_sum, Finset.sum_congr rfl fun S _ => h S,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [objFun, Finset.mul_sum]

end LayerDProto

end

#print axioms LayerDProto.permTab_mulTab
#print axioms LayerDProto.cycCount_permTab
#print axioms LayerDProto.trace_mul_rep
#print axioms LayerDProto.trace_objective4_mul_rep
