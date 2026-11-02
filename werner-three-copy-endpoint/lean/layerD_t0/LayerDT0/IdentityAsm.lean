import LayerDT0.Bridge

/-!
# Layer D (t = 0): from per-family route-2′ zeros to the certificate identity

* `orbInv_family`: an `OrbInv` vector gives, in each family, the four invariances that the proto's
  `family_zero` takes (site permutations, componentwise inversion, left and right bosonic
  multiplication).
* `family_zero_real`: `family_zero`'s conclusion over `ℂ` as a real identity.
* **`identity_of_decomp`**: if, with a nonzero scale `S`, `S · (rhs μ − lhs μ)` is the sum over the three
  families of `∑_t μ_f(t) D_f(t)` with `D_f = ∑_{P ∈ Ps f} fac_P · FTP P` (the bookkeeping that the bridge
  `pair_word` / `pair_c3` / `pair_c23` and the row and objective parts provide), and every family's `D_f`
  pairs to zero with every vector having those invariances (what `family_zero` proves from the kernel
  checks), then `lhs μ = rhs μ` for every `OrbInv` vector `μ`.
-/

open Finset

namespace LayerDT0

open WernerEndpoint LayerDProto

theorem orbInv_family {μ : Fam → Tup (Fin 3) → ℝ} (h : OrbInv (Fin 3) μ) (f : Fam) :
    (∀ π t, μ f (sitePermT π t) = μ f t) ∧ (∀ t, μ f (invT t) = μ f t) ∧
      (∀ g ∈ bos f, ∀ t, μ f (lmulT g t) = μ f t) ∧ (∀ g ∈ bos f, ∀ t, μ f (rmulT g t) = μ f t) := by
  refine ⟨fun π t => h f _ ?_ t, fun t => h f _ ?_ t, fun g hg t => h f _ ?_ t, fun g hg t => h f _ ?_ t⟩
  · exact Or.inl (Or.inl (Or.inl ⟨π, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr rfl))
  · exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
  · exact Or.inr ⟨g, hg, rfl⟩

/-- The family functional `D_f = ∑_P fac_P · FTP P`. -/
noncomputable def famD (Ps : List PartData) (t : Tup (Fin 3)) : ℤ := (Ps.map fun P => P.fac * FTP P t).sum

theorem family_zero_real {D : Tup (Fin 3) → ℤ} {x : Tup (Fin 3) → ℝ}
    (h : ∑ t, ((D t : ℤ) : ℂ) * (x t : ℂ) = 0) : ∑ t, x t * (D t : ℝ) = 0 := by
  have : ((∑ t, x t * (D t : ℝ) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  exact_mod_cast this

/-- What `family_zero` provides for a family: `D_f` pairs to zero with every invariant vector. -/
def FamZero (f : Fam) (Ps : List PartData) : Prop :=
  ∀ x : Tup (Fin 3) → ℝ, (∀ π t, x (sitePermT π t) = x t) → (∀ t, x (invT t) = x t) →
    (∀ g ∈ bos f, ∀ t, x (lmulT g t) = x t) → (∀ g ∈ bos f, ∀ t, x (rmulT g t) = x t) →
    ∑ t, ((famD Ps t : ℤ) : ℂ) * (x t : ℂ) = 0

/-- **From per-family zeros to the identity.** -/
theorem identity_of_decomp (lhs rhs : (Fam → Tup (Fin 3) → ℝ) → ℝ) (S : ℝ) (hS : S ≠ 0)
    (Ps : Fam → List PartData)
    (hdec : ∀ μ, S * (rhs μ - lhs μ) = ∑ f : Fam, ∑ t, μ f t * (famD (Ps f) t : ℝ))
    (hz : ∀ f, FamZero f (Ps f)) (μ : Fam → Tup (Fin 3) → ℝ) (hμ : OrbInv (Fin 3) μ) :
    lhs μ = rhs μ := by
  have h0 : ∑ f : Fam, ∑ t, μ f t * (famD (Ps f) t : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun f _ => ?_
    obtain ⟨h1, h2, h3, h4⟩ := orbInv_family hμ f
    exact family_zero_real (hz f (μ f) h1 h2 h3 h4)
  have := hdec μ
  rw [h0] at this
  have h' : rhs μ - lhs μ = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hS
    · exact h
  linarith

/-- `family_zero` in the form `FamZero`. -/
theorem famZero_of_grid {f : Fam} (Ps : List PartData) (bosF dc : List (Fin 24))
    (s1 : Fin 24 → List (Fin 24)) (hbosF : ∀ g ∈ bosF, permTab g ∈ bos f)
    (hmeets : meetsR bosF dc s1 = true)
    (hzero : ∀ dd ∈ dc, ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < (s1 dd).length,
      ∑ p : PF f, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt ((s1 dd).map Fin.val) dd t0 t1 i2))).sum = 0) :
    FamZero f Ps :=
  fun _ hs hi hl hr => family_zero Ps hs hi hl hr bosF dc s1 hbosF hmeets hzero

end LayerDT0

#print axioms LayerDT0.identity_of_decomp
#print axioms LayerDT0.famZero_of_grid
