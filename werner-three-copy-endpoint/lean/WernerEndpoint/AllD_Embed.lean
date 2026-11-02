import WernerEndpoint.LayerC_Twirl

/-!
# All-d lemma chain, step 2: the permutation expectations do not depend on the ambient dimension

For an injection `f : ι ↪ ι'` of local spaces, a vector `a` on one copy `(κ → ι) × ρ` is padded
with zeros to `embVec f a` on `(κ → ι') × ρ` (`embVec f a (f ∘ h, s) = a (h, s)`, zero off the
image; this is `(⊗_κ V ⊗ 1) a` for the 0/1 isometry `V = isoOfEmb f` of `Embedding.lean`).

* `isLift_embVec`: lifts go to lifts (`Tr_H|a⟩⟨a| = I/2` and the norms are unchanged).
* `gact_embVec`: padding commutes with site permutations and complex conjugation.
* `wordVal_embVec`: every word value `⟨⊗v|⊗_i P_{w_i} ⊗ P_{wq}|⊗v⟩` is unchanged.
* `tExp f a b u = Re Tr[P_uᴴ Ŷ_f(a, b)]` (the permutation expectations of the twirled moments);
  `tExp_embVec`: **the permutation expectations of a lift are the same in every ambient dimension
  `ι' ⊇ ι`** (step 2 of `all_d/README.md`). It is an exact identity, not a limit.
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Embed

variable {κ ι ι' ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι'] [Fintype ρ] [DecidableEq ρ]

/-- The embedding of one copy: `(h, s) ↦ (f ∘ h, s)`. -/
def embH (f : ι ↪ ι') : (κ → ι) × ρ → (κ → ι') × ρ := fun x => (f ∘ x.1, x.2)

theorem embH_injective (f : ι ↪ ι') : Function.Injective (embH (κ := κ) (ρ := ρ) f) := by
  intro _ _ h
  simp only [embH, Prod.mk.injEq] at h
  refine Prod.ext (funext fun i => f.injective (congrFun h.1 i)) h.2

/-- Zero padding of a vector along `embH f`. -/
def embVec (f : ι ↪ ι') (a : (κ → ι) × ρ → ℂ) : (κ → ι') × ρ → ℂ :=
  Function.extend (embH f) a 0

theorem embVec_embH (f : ι ↪ ι') (a : (κ → ι) × ρ → ℂ) (x : (κ → ι) × ρ) :
    embVec f a (embH f x) = a x :=
  (embH_injective f).extend_apply a 0 x

theorem embVec_of_not_mem (f : ι ↪ ι') (a : (κ → ι) × ρ → ℂ) {y : (κ → ι') × ρ}
    (hy : y ∉ Set.range (embH (κ := κ) (ρ := ρ) f)) : embVec f a y = 0 := by
  unfold embVec
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨x, rfl⟩; exact hy ⟨x, rfl⟩

/-- Sums of functions supported on the image of `embH f`. -/
theorem sum_embH {M : Type*} [AddCommMonoid M] (f : ι ↪ ι') (φ : (κ → ι') × ρ → M)
    (hφ : ∀ y ∉ Set.range (embH (κ := κ) (ρ := ρ) f), φ y = 0) :
    ∑ y, φ y = ∑ x, φ (embH f x) :=
  (Fintype.sum_of_injective (embH f) (embH_injective f) (fun x => φ (embH f x)) φ hφ
    (fun _ => rfl)).symm

theorem mem_range_embH_iff (f : ι ↪ ι') (h : κ → ι') (s : ρ) :
    (h, s) ∈ Set.range (embH (κ := κ) (ρ := ρ) f) ↔ h ∈ Set.range (fun h' : κ → ι => f ∘ h') := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.1, congrArg Prod.fst hx⟩
  · rintro ⟨h', rfl⟩
    exact ⟨(h', s), rfl⟩

theorem sum_site_embH {M : Type*} [AddCommMonoid M] (f : ι ↪ ι') (φ : (κ → ι') → M)
    (hφ : ∀ h ∉ Set.range (fun h' : κ → ι => f ∘ h'), φ h = 0) :
    ∑ h, φ h = ∑ h : κ → ι, φ (f ∘ h) :=
  (Fintype.sum_of_injective (fun h' : κ → ι => f ∘ h')
    (fun x y hxy => funext fun i => f.injective (congrFun hxy i)) (fun h => φ (f ∘ h)) φ hφ
    (fun _ => rfl)).symm

theorem vnormSq_embVec (f : ι ↪ ι') (a : (κ → ι) × ρ → ℂ) : vnormSq (embVec f a) = vnormSq a := by
  unfold vnormSq
  rw [sum_embH f (fun y => ‖embVec f a y‖ ^ 2) (fun y hy => by simp [embVec_of_not_mem f a hy])]
  simp only [embVec_embH]

/-- **Lifts go to lifts.** -/
theorem isLift_embVec (f : ι ↪ ι') {a b : (κ → ι) × ρ → ℂ} (h : IsLift a b) :
    IsLift (embVec f a) (embVec f b) := by
  obtain ⟨hm, ha, hb⟩ := h
  refine ⟨fun s s' => ?_, by rw [vnormSq_embVec, ha], by rw [vnormSq_embVec, hb]⟩
  rw [← hm s s', sum_site_embH f]
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [show ((f ∘ h, s) : (κ → ι') × ρ) = embH f (h, s) from rfl,
      show ((f ∘ h, s') : (κ → ι') × ρ) = embH f (h, s') from rfl, embVec_embH, embVec_embH]
  · intro h hh
    rw [embVec_of_not_mem f a (by rwa [mem_range_embH_iff]), zero_mul]

theorem eH_mem_range_iff (f : ι ↪ ι') (π : Equiv.Perm κ) (y : (κ → ι') × ρ) :
    eH π y ∈ Set.range (embH (κ := κ) (ρ := ρ) f) ↔ y ∈ Set.range (embH (κ := κ) (ρ := ρ) f) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨eH π.symm x, ?_⟩
    have : y = eH π.symm (eH π y) := (Equiv.symm_apply_apply (eH π) y).symm
    rw [this, ← hx]
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨eH π x, rfl⟩

/-- **Padding commutes with the symmetry group** (site permutations, conjugation). -/
theorem gact_embVec (f : ι ↪ ι') (g : Equiv.Perm κ × Bool) (a : (κ → ι) × ρ → ℂ) :
    gact g (embVec f a) = embVec f (gact g a) := by
  funext y
  by_cases hy : y ∈ Set.range (embH (κ := κ) (ρ := ρ) f)
  · obtain ⟨x, rfl⟩ := hy
    simp only [gact, embVec_embH]
    rw [show eH g.1 (embH f x) = embH f (eH g.1 x) from rfl, embVec_embH]
  · simp only [gact]
    rw [embVec_of_not_mem f _ hy, embVec_of_not_mem f _ (by rwa [eH_mem_range_iff]), cj_zero]

/-- The embedding of four-replica multi-indices. -/
def embX (f : ι ↪ ι') (X : Fin 4 → (κ → ι) × ρ) : Fin 4 → (κ → ι') × ρ := fun k => embH f (X k)

theorem embX_injective (f : ι ↪ ι') : Function.Injective (embX (κ := κ) (ρ := ρ) f) :=
  fun _ _ h => funext fun k => embH_injective f (congrFun h k)

theorem permIdx_embX (f : ι ↪ ι') (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (X : Fin 4 → (κ → ι) × ρ) : permIdx w wq (embX f X) = embX f (permIdx w wq X) := rfl

/-- **Word values are unchanged by the embedding.** -/
theorem wordVal_embVec (f : ι ↪ ι') (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (v : Fin 4 → (κ → ι) × ρ → ℂ) :
    wordVal w wq (fun k => embVec f (v k)) = wordVal w wq v := by
  unfold wordVal
  have hz : ∀ Y ∉ Set.range (embX (κ := κ) (ρ := ρ) f),
      star (prodVec (fun k => embVec f (v k)) Y) *
        prodVec (fun k => embVec f (v k)) (permIdx w wq Y) = 0 := by
    intro Y hY
    have : ∃ k, Y k ∉ Set.range (embH (κ := κ) (ρ := ρ) f) := by
      by_contra hc
      push_neg at hc
      choose x hx using hc
      exact hY ⟨x, funext hx⟩
    obtain ⟨k, hk⟩ := this
    have : prodVec (fun k => embVec f (v k)) Y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (embVec_of_not_mem f _ hk)
    rw [this, star_zero, zero_mul]
  rw [(Fintype.sum_of_injective (embX f) (embX_injective f) _ _ hz (fun _ => rfl)).symm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [permIdx_embX]
  simp only [prodVec, embX, embVec_embH]

theorem famVec_embVec (f : ι ↪ ι') (fam : Fam) (a b : (κ → ι) × ρ → ℂ) :
    famVec fam (embVec f a) (embVec f b) = fun k => embVec f (famVec fam a b k) := by
  funext k; simp only [famVec]; split_ifs <;> rfl

theorem trace_permOp_twirl_embVec (f : ι ↪ ι') (w : κ → Equiv.Perm (Fin 4))
    (wq : Equiv.Perm (Fin 4)) (fam : Fam) (a b : (κ → ι) × ρ → ℂ) :
    (permOp ι' ρ w wq * twirl fam (embVec f a) (embVec f b)).trace =
      (permOp ι ρ w wq * twirl fam a b).trace := by
  rw [trace_permOp_twirl, trace_permOp_twirl]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [gact_embVec, gact_embVec, famVec_embVec, wordVal_embVec]

/-- The permutation expectations `τ_f(u) = Re Tr[P_uᴴ Ŷ_f]` of the twirled moments
(`P_uᴴ = P_{u⁻¹}`). -/
def tExp (fam : Fam) (a b : (κ → ι) × ρ → ℂ) (u : Tup κ) : ℝ :=
  ((permOp ι ρ (fun i => (u.1 i)⁻¹) (u.2)⁻¹ * twirl fam a b).trace).re

/-- **Step 2.** The permutation expectations of a lift do not depend on the ambient dimension. -/
theorem tExp_embVec (f : ι ↪ ι') (fam : Fam) (a b : (κ → ι) × ρ → ℂ) (u : Tup κ) :
    tExp (ι := ι') (ρ := ρ) fam (embVec f a) (embVec f b) u = tExp (ι := ι) fam a b u := by
  unfold tExp
  rw [trace_permOp_twirl_embVec]

end Embed

end WernerEndpoint

end

#print axioms WernerEndpoint.embVec_embH
#print axioms WernerEndpoint.isLift_embVec
#print axioms WernerEndpoint.gact_embVec
#print axioms WernerEndpoint.wordVal_embVec
#print axioms WernerEndpoint.trace_permOp_twirl_embVec
#print axioms WernerEndpoint.tExp_embVec
