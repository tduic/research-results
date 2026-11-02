import WernerEndpoint.LayerC_Brauer
import WernerEndpoint.L5_Tables
import WernerEndpoint.LayerC_WalledT3a
import WernerEndpoint.LayerC_WalledT3b
import WernerEndpoint.LayerC_WalledT3c
import WernerEndpoint.LayerC_WalledT23a
import WernerEndpoint.LayerC_WalledT23b
import WernerEndpoint.LayerC_WalledT23c

/-!
# Layer C: walled closure on one site, and L6 (the diagram maps), for every local dimension

One site of the four-replica space is `(ℂ^α)^{⊗4}`; `sP α p` is the permutation operator and
`ptrans T` the partial transpose on the replicas in `T`.

* **Walled closure** `ptrans_sP_mul`: for every cut `T` the verifier uses
  (`IsCut T`: `∅, {0}, {2}, {3}, {0,1}, {0,2}, {2,3}`) and every local dimension `|α| ≥ 1`,
  `Γ_T(P_s) Γ_T(P_t) = |α|^c • Γ_T(P_u)` for some `u` and `c`. The cuts `{3}` and `{2,3}` are
  checked pair by pair by component certificates (`LayerC_Walled{T3,T23}*.lean`, kernel
  `decide`); `{0}, {2}` and `{0,1}, {0,2}` follow by relabelling replicas
  (`rearr (Equiv.sumCongr π π)`, an algebra automorphism: `rearr_sumCongr_mul`), with the
  relabelling of the diagrams checked by `decide` (`relabel_*`); `∅` is `sP_mul`.
* **L6** `rearr_sP_*`: for the six verifier tables `σ` (`L5_Tables.lean`) and their diagram maps
  `m… : Fin 24 → Fin 24` (in `PERMS` indices; these are `literal_map` of `verify_d5.py`, checked by
  `tests/test_werner_lean_walled.py`), `rearr σ (P_p) = Γ_T (P_(m p))` for every local dimension;
  `m…_surj`: each map is onto.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace WernerEndpoint

section Walled

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- `P_s P_t = P_{s t}` on one site. -/
theorem sP_mul (s t : Equiv.Perm (Fin 4)) : sP α s * sP α t = sP α (s * t) := by
  ext x z
  simp only [sP, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem ptrans_empty (A : Matrix (Fin 4 → α) (Fin 4 → α) ℂ) :
    ptrans (ι := fun _ : Fin 4 => α) ∅ A = A := by
  ext x y
  simp [ptrans]

theorem ptrans_sP_eq_br (T : Finset (Fin 4)) (i : Fin 24) :
    ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab i)) = br α (muT T i) := by
  rw [← br_permMatch, ptrans_br]
  rfl

theorem chkT3 : ∀ i j : Fin 24, chkB certRowT3 muRowT3 i j = true := by
  intro i j
  fin_cases i
  exacts [chkT3_0 j, chkT3_1 j, chkT3_2 j, chkT3_3 j, chkT3_4 j, chkT3_5 j, chkT3_6 j,
    chkT3_7 j, chkT3_8 j, chkT3_9 j, chkT3_10 j, chkT3_11 j, chkT3_12 j, chkT3_13 j, chkT3_14 j,
    chkT3_15 j, chkT3_16 j, chkT3_17 j, chkT3_18 j, chkT3_19 j, chkT3_20 j, chkT3_21 j,
    chkT3_22 j, chkT3_23 j]

theorem chkT23 : ∀ i j : Fin 24, chkB certRowT23 muRowT23 i j = true := by
  intro i j
  fin_cases i
  exacts [chkT23_0 j, chkT23_1 j, chkT23_2 j, chkT23_3 j, chkT23_4 j, chkT23_5 j, chkT23_6 j,
    chkT23_7 j, chkT23_8 j, chkT23_9 j, chkT23_10 j, chkT23_11 j, chkT23_12 j, chkT23_13 j,
    chkT23_14 j, chkT23_15 j, chkT23_16 j, chkT23_17 j, chkT23_18 j, chkT23_19 j, chkT23_20 j,
    chkT23_21 j, chkT23_22 j, chkT23_23 j]

/-- A checked table of certificates gives closure of the cut. -/
theorem ptrans_sP_mul_of_chk [Nonempty α] {T : Finset (Fin 4)} {rows muRow : Fin 24 → ℕ}
    (hmu : ∀ i q, muC muRow i q = muT T i q) (hchk : ∀ i j, chkB rows muRow i j = true)
    (i j : Fin 24) :
    ∃ (u : Fin 24) (c : ℕ),
      ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab i)) *
          ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab j)) =
        ((Fintype.card α ^ c : ℕ) : ℂ) • ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab u)) := by
  refine ⟨(certOf rows i j).u, (certOf rows i j).c, ?_⟩
  rw [ptrans_sP_eq_br, ptrans_sP_eq_br, ptrans_sP_eq_br]
  exact br_mul_br (chkB_sound hmu (hchk i j))

/-! ### Relabelling replicas -/

/-- Relabelling the replicas by `π` is an algebra automorphism. -/
theorem rearr_sumCongr_mul (π : Equiv.Perm (Fin 4)) (A B : Matrix (Fin 4 → α) (Fin 4 → α) ℂ) :
    rearr (Equiv.sumCongr π π) (A * B) =
      rearr (Equiv.sumCongr π π) A * rearr (Equiv.sumCongr π π) B := by
  ext x y
  simp only [rearr, Matrix.of_apply, Matrix.mul_apply]
  let e : (Fin 4 → α) ≃ (Fin 4 → α) :=
    { toFun := fun z => fun s => z (π s)
      invFun := fun z => fun s => z (π.symm s)
      left_inv := fun z => funext fun s => by simp
      right_inv := fun z => funext fun s => by simp }
  exact (Equiv.sum_comp e _).symm

/-- Closure transported along a relabelling of replicas. -/
theorem closure_relabel [Nonempty α] (π : Equiv.Perm (Fin 4)) {T T' : Finset (Fin 4)}
    (hT : ∀ i j : Fin 24, ∃ (u : Fin 24) (c : ℕ),
      ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab i)) *
          ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab j)) =
        ((Fintype.card α ^ c : ℕ) : ℂ) • ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab u)))
    (hfwd : ∀ i : Fin 24, ∃ i' : Fin 24, ∀ q,
      Equiv.sumCongr π π (muT T i ((Equiv.sumCongr π π).symm q)) = muT T' i' q)
    (hbwd : ∀ i' : Fin 24, ∃ i : Fin 24, ∀ q,
      Equiv.sumCongr π π (muT T i ((Equiv.sumCongr π π).symm q)) = muT T' i' q)
    (i' j' : Fin 24) :
    ∃ (u : Fin 24) (c : ℕ),
      ptrans (ι := fun _ : Fin 4 => α) T' (sP α (permTab i')) *
          ptrans (ι := fun _ : Fin 4 => α) T' (sP α (permTab j')) =
        ((Fintype.card α ^ c : ℕ) : ℂ) • ptrans (ι := fun _ : Fin 4 => α) T' (sP α (permTab u)) := by
  have key : ∀ i i' : Fin 24, (∀ q, Equiv.sumCongr π π (muT T i ((Equiv.sumCongr π π).symm q)) =
      muT T' i' q) →
      rearr (Equiv.sumCongr π π) (ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab i))) =
        ptrans (ι := fun _ : Fin 4 => α) T' (sP α (permTab i')) := by
    intro i i' h
    rw [ptrans_sP_eq_br, ptrans_sP_eq_br, rearr_br]
    exact br_congr h
  obtain ⟨i, hi⟩ := hbwd i'
  obtain ⟨j, hj⟩ := hbwd j'
  obtain ⟨u, c, huc⟩ := hT i j
  obtain ⟨u', hu'⟩ := hfwd u
  refine ⟨u', c, ?_⟩
  rw [← key i i' hi, ← key j j' hj, ← key u u' hu', ← rearr_sumCongr_mul, huc, rearr_smul]

/-- The seven cuts of `verify_d5.py`'s word and coupled blocks. -/
def IsCut (T : Finset (Fin 4)) : Prop :=
  T = ∅ ∨ T = {0} ∨ T = {2} ∨ T = {3} ∨ T = {0, 1} ∨ T = {0, 2} ∨ T = {2, 3}

theorem relabel_T0_fwd : ∀ i : Fin 24, ∃ i' : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 0 3)
    (Equiv.swap 0 3) (muT {3} i ((Equiv.sumCongr (Equiv.swap 0 3) (Equiv.swap 0 3)).symm q)) =
      muT {0} i' q := by decide +kernel
theorem relabel_T0_bwd : ∀ i' : Fin 24, ∃ i : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 0 3)
    (Equiv.swap 0 3) (muT {3} i ((Equiv.sumCongr (Equiv.swap 0 3) (Equiv.swap 0 3)).symm q)) =
      muT {0} i' q := by decide +kernel
theorem relabel_T2_fwd : ∀ i : Fin 24, ∃ i' : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 2 3)
    (Equiv.swap 2 3) (muT {3} i ((Equiv.sumCongr (Equiv.swap 2 3) (Equiv.swap 2 3)).symm q)) =
      muT {2} i' q := by decide +kernel
theorem relabel_T2_bwd : ∀ i' : Fin 24, ∃ i : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 2 3)
    (Equiv.swap 2 3) (muT {3} i ((Equiv.sumCongr (Equiv.swap 2 3) (Equiv.swap 2 3)).symm q)) =
      muT {2} i' q := by decide +kernel
theorem relabel_T02_fwd : ∀ i : Fin 24, ∃ i' : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 0 3)
    (Equiv.swap 0 3) (muT {2, 3} i ((Equiv.sumCongr (Equiv.swap 0 3) (Equiv.swap 0 3)).symm q)) =
      muT {0, 2} i' q := by decide +kernel
theorem relabel_T02_bwd : ∀ i' : Fin 24, ∃ i : Fin 24, ∀ q, Equiv.sumCongr (Equiv.swap 0 3)
    (Equiv.swap 0 3) (muT {2, 3} i ((Equiv.sumCongr (Equiv.swap 0 3) (Equiv.swap 0 3)).symm q)) =
      muT {0, 2} i' q := by decide +kernel

/-- `(0 2)(1 3)`. -/
def swap0213 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem relabel_T01_fwd : ∀ i : Fin 24, ∃ i' : Fin 24, ∀ q, Equiv.sumCongr swap0213
    swap0213 (muT {2, 3} i ((Equiv.sumCongr swap0213 swap0213).symm q)) =
      muT {0, 1} i' q := by decide +kernel
theorem relabel_T01_bwd : ∀ i' : Fin 24, ∃ i : Fin 24, ∀ q, Equiv.sumCongr swap0213
    swap0213 (muT {2, 3} i ((Equiv.sumCongr swap0213 swap0213).symm q)) =
      muT {0, 1} i' q := by decide +kernel

theorem closure_index [Nonempty α] {T : Finset (Fin 4)} (hT : IsCut T) (i j : Fin 24) :
    ∃ (u : Fin 24) (c : ℕ),
      ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab i)) *
          ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab j)) =
        ((Fintype.card α ^ c : ℕ) : ℂ) • ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab u)) := by
  have h3 := ptrans_sP_mul_of_chk α muC_T3 chkT3
  have h23 := ptrans_sP_mul_of_chk α muC_T23 chkT23
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨u, hu⟩ := permTab_surj (permTab i * permTab j)
    refine ⟨u, 0, ?_⟩
    rw [ptrans_empty, ptrans_empty, ptrans_empty, sP_mul, hu]
    simp
  · exact closure_relabel α _ h3 relabel_T0_fwd relabel_T0_bwd i j
  · exact closure_relabel α _ h3 relabel_T2_fwd relabel_T2_bwd i j
  · exact h3 i j
  · exact closure_relabel α _ h23 relabel_T01_fwd relabel_T01_bwd i j
  · exact closure_relabel α _ h23 relabel_T02_fwd relabel_T02_bwd i j
  · exact h23 i j

/-- **Walled closure on one site.** For every cut of the verifier and every local dimension
`|α| ≥ 1`: `Γ_T(P_s) Γ_T(P_t) = |α|^c Γ_T(P_u)`. -/
theorem ptrans_sP_mul [Nonempty α] {T : Finset (Fin 4)} (hT : IsCut T) (s t : Equiv.Perm (Fin 4)) :
    ∃ (u : Equiv.Perm (Fin 4)) (c : ℕ),
      ptrans (ι := fun _ : Fin 4 => α) T (sP α s) * ptrans (ι := fun _ : Fin 4 => α) T (sP α t) =
        ((Fintype.card α ^ c : ℕ) : ℂ) • ptrans (ι := fun _ : Fin 4 => α) T (sP α u) := by
  obtain ⟨i, rfl⟩ := permTab_surj s
  obtain ⟨j, rfl⟩ := permTab_surj t
  obtain ⟨u, c, h⟩ := closure_index α hT i j
  exact ⟨_, c, h⟩

end Walled

/-! ### L6: the six diagram maps -/

/-- L6 from a slot-map identity. -/
theorem rearr_sP_of_slot {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (T : Finset (Fin 4)) (p q : Equiv.Perm (Fin 4))
    (h : ∀ x, σ (permMatch p (σ.symm x)) = tauT T (permMatch q (tauT T x))) :
    rearr σ (sP α p) = ptrans (ι := fun _ : Fin 4 => α) T (sP α q) := by
  rw [← br_permMatch, ← br_permMatch, rearr_br, ptrans_br]
  exact br_congr h

/-- `MAPS["c3"]["31"]` of `verify_d5.py` in `PERMS` indices. -/
def mT3_31 : Fin 24 → Fin 24 :=
  ![11, 9, 21, 23, 15, 17, 5, 3, 19, 22, 13, 16, 0, 2, 6, 8, 12, 14, 1, 4, 7, 10, 18, 20]
/-- `MAPS["c3"]["13"]` (the same list as the u-map). -/
def mT3_13 : Fin 24 → Fin 24 :=
  ![11, 9, 21, 23, 15, 17, 5, 3, 19, 22, 13, 16, 0, 2, 6, 8, 12, 14, 1, 4, 7, 10, 18, 20]
/-- `MAPS["c3"]["22"]`. -/
def mT3_22 : Fin 24 → Fin 24 :=
  ![17, 23, 11, 21, 9, 15, 16, 22, 5, 19, 3, 13, 10, 20, 4, 18, 1, 7, 8, 14, 2, 12, 0, 6]
/-- `MAPS["c23"]["31"]`. -/
def mT23_31 : Fin 24 → Fin 24 :=
  ![4, 18, 2, 12, 23, 17, 5, 19, 0, 6, 21, 11, 3, 13, 1, 7, 15, 9, 22, 16, 20, 10, 14, 8]
/-- `MAPS["c23"]["13"]`. -/
def mT23_13 : Fin 24 → Fin 24 :=
  ![8, 10, 14, 16, 20, 22, 2, 4, 12, 17, 18, 23, 0, 5, 6, 11, 19, 21, 1, 3, 7, 9, 13, 15]
/-- `MAPS["c23"]["22"]`. -/
def mT23_22 : Fin 24 → Fin 24 :=
  ![2, 12, 23, 17, 18, 4, 3, 13, 9, 15, 7, 1, 22, 16, 8, 14, 10, 20, 19, 5, 6, 0, 11, 21]

theorem slotT3_31 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT3_31 (permMatch (permTab i) (sigmaT3_31.symm x)) =
      tauT {3} (permMatch (permTab (mT3_31 i)) (tauT {3} x)) := by decide +kernel
theorem slotT3_13 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT3_13 (permMatch (permTab i) (sigmaT3_13.symm x)) =
      tauT {3} (permMatch (permTab (mT3_13 i)) (tauT {3} x)) := by decide +kernel
theorem slotT3_22 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT3_22 (permMatch (permTab i) (sigmaT3_22.symm x)) =
      tauT {3} (permMatch (permTab (mT3_22 i)) (tauT {3} x)) := by decide +kernel
theorem slotT23_31 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT23_31 (permMatch (permTab i) (sigmaT23_31.symm x)) =
      tauT {2, 3} (permMatch (permTab (mT23_31 i)) (tauT {2, 3} x)) := by decide +kernel
theorem slotT23_13 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT23_13 (permMatch (permTab i) (sigmaT23_13.symm x)) =
      tauT {2, 3} (permMatch (permTab (mT23_13 i)) (tauT {2, 3} x)) := by decide +kernel
theorem slotT23_22 : ∀ (i : Fin 24) (x : Fin 4 ⊕ Fin 4),
    sigmaT23_22 (permMatch (permTab i) (sigmaT23_22.symm x)) =
      tauT {2, 3} (permMatch (permTab (mT23_22 i)) (tauT {2, 3} x)) := by decide +kernel

theorem mT3_31_surj : ∀ j : Fin 24, ∃ i, mT3_31 i = j := by decide
theorem mT3_13_surj : ∀ j : Fin 24, ∃ i, mT3_13 i = j := by decide
theorem mT3_22_surj : ∀ j : Fin 24, ∃ i, mT3_22 i = j := by decide
theorem mT23_31_surj : ∀ j : Fin 24, ∃ i, mT23_31 i = j := by decide
theorem mT23_13_surj : ∀ j : Fin 24, ∃ i, mT23_13 i = j := by decide
theorem mT23_22_surj : ∀ j : Fin 24, ∃ i, mT23_22 i = j := by decide

section L6

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- **L6, one site, `MAPS["c3"]["31"]`.** `rearr σ (P_p) = Γ_{3}(P_(m p))`, every dimension. -/
theorem rearr_sP_T3_31 (i : Fin 24) : rearr sigmaT3_31 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {3} (sP α (permTab (mT3_31 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT3_31 i)
/-- **L6, one site, `MAPS["c3"]["13"]`.** -/
theorem rearr_sP_T3_13 (i : Fin 24) : rearr sigmaT3_13 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {3} (sP α (permTab (mT3_13 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT3_13 i)
/-- **L6, one site, `MAPS["c3"]["22"]`.** -/
theorem rearr_sP_T3_22 (i : Fin 24) : rearr sigmaT3_22 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {3} (sP α (permTab (mT3_22 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT3_22 i)
/-- **L6, one site, `MAPS["c23"]["31"]`.** -/
theorem rearr_sP_T23_31 (i : Fin 24) : rearr sigmaT23_31 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {2, 3} (sP α (permTab (mT23_31 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT23_31 i)
/-- **L6, one site, `MAPS["c23"]["13"]`.** -/
theorem rearr_sP_T23_13 (i : Fin 24) : rearr sigmaT23_13 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {2, 3} (sP α (permTab (mT23_13 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT23_13 i)
/-- **L6, one site, `MAPS["c23"]["22"]`.** -/
theorem rearr_sP_T23_22 (i : Fin 24) : rearr sigmaT23_22 (sP α (permTab i)) =
    ptrans (ι := fun _ : Fin 4 => α) {2, 3} (sP α (permTab (mT23_22 i))) :=
  rearr_sP_of_slot _ _ _ _ (slotT23_22 i)

end L6

end WernerEndpoint

#print axioms WernerEndpoint.sP_mul
#print axioms WernerEndpoint.rearr_sumCongr_mul
#print axioms WernerEndpoint.closure_relabel
#print axioms WernerEndpoint.closure_index
#print axioms WernerEndpoint.ptrans_sP_mul
#print axioms WernerEndpoint.rearr_sP_T3_31
#print axioms WernerEndpoint.rearr_sP_T3_13
#print axioms WernerEndpoint.rearr_sP_T3_22
#print axioms WernerEndpoint.rearr_sP_T23_31
#print axioms WernerEndpoint.rearr_sP_T23_13
#print axioms WernerEndpoint.rearr_sP_T23_22
#print axioms WernerEndpoint.mT3_31_surj
#print axioms WernerEndpoint.mT3_13_surj
#print axioms WernerEndpoint.mT3_22_surj
#print axioms WernerEndpoint.mT23_31_surj
#print axioms WernerEndpoint.mT23_13_surj
#print axioms WernerEndpoint.mT23_22_surj
