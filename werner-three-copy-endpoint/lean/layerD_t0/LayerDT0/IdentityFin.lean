import LayerDT0.Totals

/-!
# Layer D (t = 0): part lists with equal cores

`map_core_eq`: two part lists of length `n` whose `i`-th parts have equal cores for every `i` in a list `idx`
equal to `List.range n` have equal core lists. The generated `Gen/Id/F<f>/Core.lean` applies it with one
`decide +kernel` lemma per part (`ce<i>`) to turn the generated `famZero` into `FamZero f (PsT0 f)`
(`famZero_congr`).
-/

namespace LayerDT0

open LayerDProto

instance : Inhabited PartData := ⟨⟨[], 0, [], [], [], 0, [], 0, 0, [], [], []⟩⟩

/-- Field-by-field core comparison (a `Bool`, so that the kernel can decide it). -/
def coreEqB (P Q : PartData) : Bool :=
  decide (P.ks = Q.ks) && decide (P.k = Q.k) && decide (P.X = Q.X) && decide (P.Bl = Q.Bl) &&
    decide (P.Br = Q.Br) && decide (P.fac = Q.fac) && decide (P.rhos = Q.rhos)

theorem core_of_coreEqB {P Q : PartData} (h : coreEqB P Q = true) : PartData.core P = PartData.core Q := by
  simp only [coreEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [PartData.core, h1, h2, h3, h4, h5, h6, h7]

theorem map_core_eq {Ps Qs : List PartData} (n : ℕ) (hP : Ps.length = n) (hQ : Qs.length = n) (idx : List ℕ)
    (hidx : idx = List.range n)
    (h : ∀ i ∈ idx, PartData.core (Ps.getD i default) = PartData.core (Qs.getD i default)) :
    Ps.map PartData.core = Qs.map PartData.core := by
  subst hidx
  apply List.ext_getElem
  · simp [hP, hQ]
  · intro i h1 h2
    simp only [List.getElem_map]
    have hi : i < n := by simpa [hP] using h1
    have := h i (List.mem_range.2 hi)
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this

end LayerDT0

#print axioms LayerDT0.map_core_eq
#print axioms LayerDT0.core_of_coreEqB
