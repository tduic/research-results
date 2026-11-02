import LayerDProto.R2Assembly

/-!
# Layer D, (E′): the families' bosonic lists and grids, in the form the assembly uses

`bosN31` (families 31 and 13) and `bosN22` are the bosonic groups as index lists, with the facts
`family_at_d` needs (`decide`). The tree grids are `SymWerner`'s `dc31`/`s1_31` and `dc22`/`s1_22`.
-/

open WernerEndpoint


namespace LayerDProto

theorem bosN31_f31 : ∀ c ∈ bosN31, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos .f31 := by decide +kernel
theorem bosN31_f13 : ∀ c ∈ bosN31, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos .f13 := by decide +kernel
theorem bosN22_f22 : ∀ c ∈ bosN22, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos .f22 := by decide +kernel

theorem bosN31_comp31 : ∀ c : Fin 24, permTab c ∈ bos .f31 → (c : ℕ) ∈ bosN31 := by decide +kernel
theorem bosN31_comp13 : ∀ c : Fin 24, permTab c ∈ bos .f13 → (c : ℕ) ∈ bosN31 := by decide +kernel
theorem bosN22_comp22 : ∀ c : Fin 24, permTab c ∈ bos .f22 → (c : ℕ) ∈ bosN22 := by decide +kernel

theorem nodup_flatMap_key {α β : Type*} (l : List α) (f : α → List β) (key : β → α)
    (hl : l.Nodup) (hk : ∀ a, ∀ y ∈ f a, key y = a) (hf : ∀ a ∈ l, (f a).Nodup) : (l.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hf, ?_⟩
  refine List.Pairwise.imp (fun {a b} hab => ?_) hl
  intro y hya hyb
  exact hab ((hk a y hya).symm.trans (hk b y hyb))

theorem hcodes_nodup (bosL : List ℕ) (h : bosL.Nodup) : (hcodes bosL).Nodup := by
  unfold hcodes
  refine nodup_flatMap_key _ _ (fun y => y.1) (by decide) (fun a y hy => ?_) (fun σ _ => ?_)
  · simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hy; rfl
  refine nodup_flatMap_key _ _ (fun y => y.2.1) (by decide) (fun a y hy => ?_) (fun ε _ => ?_)
  · simp only [List.mem_flatMap, List.mem_map] at hy
    obtain ⟨_, _, _, _, rfl⟩ := hy; rfl
  refine nodup_flatMap_key _ _ (fun y => y.2.2.1) h (fun a y hy => ?_) (fun g _ => ?_)
  · simp only [List.mem_map] at hy
    obtain ⟨_, _, rfl⟩ := hy; rfl
  exact h.map fun a b hab => by simpa using hab

theorem hcodes31_nodup : (hcodes bosN31).Nodup := hcodes_nodup _ (by decide)
theorem hcodes22_nodup : (hcodes bosN22).Nodup := hcodes_nodup _ (by decide)


end LayerDProto


#print axioms LayerDProto.bosN31_comp13
#print axioms LayerDProto.hcodes31_nodup

namespace LayerDProto

theorem sum_zip_fst {α β : Type*} (Ps : List α) (Qs : List β) (h : Ps.length ≤ Qs.length) (g : α → ℤ) :
    ((Ps.zip Qs).map fun x => g x.1).sum = (Ps.map g).sum := by
  show ((Ps.zip Qs).map (g ∘ Prod.fst)).sum = _
  rw [← List.map_map, List.map_fst_zip h]

end LayerDProto
