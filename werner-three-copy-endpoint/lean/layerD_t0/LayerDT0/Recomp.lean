import LayerDT0.Totals
import LayerDProto.R2Recomp

/-!
# Layer D (t = 0): family zeros through re-presented parts (coupled blocks)

The fold data of a coupled part cannot be built on its own presentation (`B_u`, `B_v` are never of full
column rank), so the generated family lists carry a re-presented copy `P'` of such a part
(`layerD_proto/recompress.py`: `Y = L Z Rᵀ`, `L`, `R` of full column rank) and the kernel checks
`ycoreOK w P P'` (`R2RecompKernel.lean`). This file carries `FamZero` from the generated list back to the
original one:

* `YRel P P'`: same `fac` and same functional `FTP`; from `ycoreOK` (`yRel_of_ycoreOK`), from equal cores
  (`yRel_of_core`, or `yRel_of_sameCoreOK` from the `Bool` check, for the parts that are not re-presented) or by
  reflexivity.
* `famD_ycongr`, **`famZero_ycongr`**: lists related part by part (`List.Forall₂ YRel`) have the same `famD`,
  so `FamZero f Ps'` gives `FamZero f Ps`.
-/

namespace LayerDT0

open WernerEndpoint LayerDProto

/-- `P'` has the same coefficient and the same functional as `P`. -/
def YRel (P P' : PartData) : Prop := P.fac = P'.fac ∧ FTP P = FTP P'

theorem yRel_refl (P : PartData) : YRel P P := ⟨rfl, rfl⟩

theorem yRel_of_ycoreOK {w : ℕ} {P P' : PartData} (h : ycoreOK w P P' = true) : YRel P P' :=
  FTP_ycongr w P P' h

theorem yRel_of_core {P P' : PartData} (h : PartData.core P = PartData.core P') : YRel P P' := by
  simp only [PartData.core, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h6, funext fun t => ?_⟩
  unfold FTP
  rw [h1, h2, h3, h4, h5, h7]

theorem yRel_of_sameCoreOK {P P' : PartData} (h : sameCoreOK P P' = true) : YRel P P' := by
  simp only [sameCoreOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h6, funext fun t => ?_⟩
  unfold FTP
  rw [h1, h2, h3, h4, h5, h7]

theorem yRel_symm {P P' : PartData} (h : YRel P P') : YRel P' P := ⟨h.1.symm, h.2.symm⟩

theorem yRel_trans {P P' P'' : PartData} (h : YRel P P') (h' : YRel P' P'') : YRel P P'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- Index-wise: lists of length `n` whose `i`-th parts are related for every `i ∈ idx = List.range n`
(`d0` is the `getD` default, e.g. `default`). -/
theorem forall2_yRel_of_getD {Ps Qs : List PartData} (n : ℕ) (hP : Ps.length = n) (hQ : Qs.length = n)
    (d0 : PartData) (idx : List ℕ) (hidx : idx = List.range n)
    (h : ∀ i ∈ idx, YRel (Ps.getD i d0) (Qs.getD i d0)) : List.Forall₂ YRel Ps Qs := by
  subst hidx
  rw [List.forall₂_iff_get]
  refine ⟨by rw [hP, hQ], fun i h1 h2 => ?_⟩
  have := h i (List.mem_range.2 (by omega))
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem famD_ycongr {Ps Ps' : List PartData} (h : List.Forall₂ YRel Ps Ps') : famD Ps = famD Ps' := by
  funext t
  unfold famD
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    obtain ⟨h1, h2⟩ := hab
    simp only [List.map_cons, List.sum_cons]
    rw [h1, h2, ih]

/-- **`FamZero` through re-presented parts.** -/
theorem famZero_ycongr {f : Fam} {Ps Ps' : List PartData} (h : List.Forall₂ YRel Ps Ps')
    (hz : FamZero f Ps') : FamZero f Ps := by
  intro x h1 h2 h3 h4
  rw [famD_ycongr h]
  exact hz x h1 h2 h3 h4

end LayerDT0

#print axioms LayerDT0.famZero_ycongr
#print axioms LayerDT0.yRel_of_ycoreOK
#print axioms LayerDT0.yRel_of_core
#print axioms LayerDT0.yRel_of_sameCoreOK
#print axioms LayerDT0.forall2_yRel_of_getD
