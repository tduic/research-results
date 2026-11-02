import LayerDProto.SymReduce
import LayerDProto.TraceRows
import WernerEndpoint.LayerC_Twirl

/-!
# Layer D, (E′): the `Sym_H` reduction for the Werner families

The group of a family `f` is parametrized by `P f = {(σ, ε, g, g') : g, g' ∈ bos f}` acting on diagram
tuples by

`actF (σ, ε, g, g') = lmulT g * rmulT g' * (invT if ε) * sitePermT σ`,  i.e.
`(actF p t)_i = g · ε(t_{σ i}) · g'`, `(actF p t)_q = g · ε(t_q) · g'`,

a product of layer C's orbit generators. So the coefficients `x` of `twirl_rep` are invariant under
every `actF p` (`x_actF`). The family is closed under composition (`actF_mul`: `actF p ∘ actF q =
actF (mulP p q)`) and `p ↦ mulP p q` is a bijection of `P f` (`mulP_bijective`). `SymReduce` then
gives:

* `sum_mul_eq_zero_of_symF`: if `∑_{p ∈ P f} D (actF p t) = 0` for every `t` in a set `R` that meets
  every orbit, then `∑_t D t · x t = 0`;
* `meetsR_sound`: the tree grid `R = {t : t_q ∈ dc, t₂ ∈ s1 t_q}` (index lists) meets every orbit
  as soon as the Boolean check `meetsR` succeeds; `meetsR_31` (families 31 and 13) and `meetsR_22` are that
  check for the verifier's grids (`route2.tree_grid`), by `decide`.

The index form of the action (`actIdx`, with `mulTab` and `invTab`) is what the kernel evaluates;
`tupEquiv_actIdx` connects the two.
-/

open WernerEndpoint

namespace LayerDProto

/-! ### The parameters and the action -/

instance (f : Fam) : DecidablePred (· ∈ bos f) := fun g =>
  decidable_of_iff (∀ k, famPat f (g k) = famPat f k) Iff.rfl

theorem bos_mul {f : Fam} {g h : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (hh : h ∈ bos f) :
    g * h ∈ bos f := by
  intro k
  rw [Equiv.Perm.mul_apply, hg, hh]

/-- The raw parameters `(σ, ε, g, g')`. -/
abbrev HPar := Equiv.Perm (Fin 3) × Bool × Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)

/-- The parameters of the family's group. -/
def PF (f : Fam) := {p : HPar // p.2.2.1 ∈ bos f ∧ p.2.2.2 ∈ bos f}

instance (f : Fam) : Fintype (PF f) := by unfold PF; infer_instance

/-- `ε`: identity or inversion of all components. -/
def epsT (ε : Bool) : Equiv.Perm (Tup (Fin 3)) := if ε then invT else 1

/-- The action of a parameter, as a product of layer C's orbit generators. -/
def actF (p : HPar) : Equiv.Perm (Tup (Fin 3)) :=
  lmulT p.2.2.1 * rmulT p.2.2.2 * epsT p.2.1 * sitePermT p.1

/-- `e ε s` is `s` or `s⁻¹`. -/
def eInv (ε : Bool) (s : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 4) := if ε then s⁻¹ else s

theorem actF_apply (p : HPar) (t : Tup (Fin 3)) :
    actF p t = (fun i => p.2.2.1 * eInv p.2.1 (t.1 (p.1 i)) * p.2.2.2,
      p.2.2.1 * eInv p.2.1 t.2 * p.2.2.2) := by
  obtain ⟨σ, ε, g, g'⟩ := p
  cases ε <;> simp [actF, epsT, eInv, lmulT, rmulT, invT, sitePermT, Equiv.Perm.mul_apply, mul_assoc]

/-- The composition law: `actF p ∘ actF q = actF (mulP p q)`. -/
def mulP (p q : HPar) : HPar :=
  (q.1 * p.1, xor p.2.1 q.2.1,
    if p.2.1 then p.2.2.1 * q.2.2.2⁻¹ else p.2.2.1 * q.2.2.1,
    if p.2.1 then q.2.2.1⁻¹ * p.2.2.2 else q.2.2.2 * p.2.2.2)

theorem actF_mul (p q : HPar) (t : Tup (Fin 3)) : actF p (actF q t) = actF (mulP p q) t := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨τ, δ, h, h'⟩ := q
  rw [actF_apply, actF_apply, actF_apply]
  cases ε <;> cases δ <;>
    simp [mulP, eInv, Equiv.Perm.mul_apply, mul_assoc, mul_inv_rev]

theorem mulP_mem {f : Fam} (p q : PF f) : (mulP p.1 q.1).2.2.1 ∈ bos f ∧ (mulP p.1 q.1).2.2.2 ∈ bos f := by
  obtain ⟨⟨σ, ε, g, g'⟩, hg, hg'⟩ := p
  obtain ⟨⟨τ, δ, h, h'⟩, hh, hh'⟩ := q
  cases ε
  · exact ⟨bos_mul hg hh, bos_mul hh' hg'⟩
  · exact ⟨bos_mul hg (bos_inv hh'), bos_mul (bos_inv hh) hg'⟩

/-- `mulP` on the family's parameters. -/
def mulPF {f : Fam} (p q : PF f) : PF f := ⟨mulP p.1 q.1, mulP_mem p q⟩

theorem mulPF_injective {f : Fam} (q : PF f) : Function.Injective fun p : PF f => mulPF p q := by
  obtain ⟨⟨τ, δ, h₁, h₂⟩, -⟩ := q
  rintro ⟨⟨σ, ε, g, g'⟩, hp⟩ ⟨⟨σ', ε', k, k'⟩, hp'⟩ hpq
  have h' := congrArg Subtype.val hpq
  simp only [mulPF, mulP, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  have hσ : σ = σ' := mul_left_cancel h1
  have hε : ε = ε' := by cases ε <;> cases ε' <;> cases δ <;> simp_all
  subst hσ hε
  apply Subtype.ext
  cases ε
  · simp only [Bool.false_eq_true, if_false] at h3 h4
    simp [mul_right_cancel h3, mul_left_cancel h4]
  · simp only [if_true] at h3 h4
    simp [mul_right_cancel h3, mul_left_cancel h4]

theorem mulPF_bijective {f : Fam} (q : PF f) : Function.Bijective fun p : PF f => mulPF p q :=
  (Finite.injective_iff_bijective).mp (mulPF_injective q)

/-- The coefficients of `twirl_rep` are invariant under the whole parametrized group. -/
theorem x_actF {f : Fam} {x : Tup (Fin 3) → ℝ}
    (hs : ∀ π t, x (sitePermT π t) = x t) (hi : ∀ t, x (invT t) = x t)
    (hl : ∀ g ∈ bos f, ∀ t, x (lmulT g t) = x t) (hr : ∀ g ∈ bos f, ∀ t, x (rmulT g t) = x t)
    (p : PF f) (t : Tup (Fin 3)) : x (actF p.1 t) = x t := by
  obtain ⟨⟨σ, ε, g, g'⟩, hg, hg'⟩ := p
  simp only [actF, Equiv.Perm.mul_apply]
  rw [hl g hg, hr g' hg']
  cases ε
  · simp [epsT, hs]
  · simp [epsT, hi, hs]

/-- **(E′) ⇒ the identity on the twirl.** If `∑_{p ∈ P f} D (actF p t) = 0` on a set `R` meeting every
orbit of the parametrized group, then `∑_t D t · x t = 0` for the real coefficients `x` of `twirl_rep`. -/
theorem sum_mul_eq_zero_of_symF {f : Fam} (D : Tup (Fin 3) → ℂ) {x : Tup (Fin 3) → ℝ}
    (hs : ∀ π t, x (sitePermT π t) = x t) (hi : ∀ t, x (invT t) = x t)
    (hl : ∀ g ∈ bos f, ∀ t, x (lmulT g t) = x t) (hr : ∀ g ∈ bos f, ∀ t, x (rmulT g t) = x t)
    (R : Tup (Fin 3) → Prop) (hR : ∀ t, ∃ q : PF f, R (actF q.1 t))
    (h0 : ∀ t, R t → ∑ p : PF f, D (actF p.1 t) = 0) :
    ∑ t, D t * (x t : ℂ) = 0 := by
  haveI : Nonempty (PF f) := ⟨⟨(1, false, 1, 1), fun k => rfl, fun k => rfl⟩⟩
  exact Sym.sum_mul_eq_zero_of_sym (fun p : PF f => actF p.1) mulPF
    (fun p q t => actF_mul p.1 q.1 t) mulPF_bijective D (fun t => (x t : ℂ))
    (fun p t => by show ((x (actF p.1 t) : ℝ) : ℂ) = (x t : ℂ); rw [x_actF hs hi hl hr p t]) R hR h0

/-! ### Index form -/

/-- The index form of a parameter: `(σ, ε, g, g')` with `g, g'` as `PERMS` indices. -/
abbrev IPar := Equiv.Perm (Fin 3) × Bool × Fin 24 × Fin 24

def toHPar (p : IPar) : HPar := (p.1, p.2.1, permTab p.2.2.1, permTab p.2.2.2)

/-- The kernel's action on index tuples: `g · ε(t_{σ i}) · g'` with `mulTab`, `invTab`. -/
def eIdx (ε : Bool) (s : Fin 24) : Fin 24 := if ε then invTab s else s

def actIdx (p : IPar) (t : (Fin 3 → Fin 24) × Fin 24) : (Fin 3 → Fin 24) × Fin 24 :=
  (fun i => mulTab (mulTab p.2.2.1 (eIdx p.2.1 (t.1 (p.1 i)))) p.2.2.2,
    mulTab (mulTab p.2.2.1 (eIdx p.2.1 t.2)) p.2.2.2)

theorem permTab_eIdx (ε : Bool) (s : Fin 24) : permTab (eIdx ε s) = eInv ε (permTab s) := by
  cases ε <;> simp [eIdx, eInv, permTab_invTab]

theorem tupEquiv_actIdx (p : IPar) (t : (Fin 3 → Fin 24) × Fin 24) :
    tupEquiv (actIdx p t) = actF (toHPar p) (tupEquiv t) := by
  rw [actF_apply, tupEquiv_apply, tupEquiv_apply]
  simp [actIdx, toHPar, permTab_mulTab, permTab_eIdx]

/-! ### The tree grid meets every orbit -/

/-- Boolean check: for all index pairs `(a, b) = (t₂, t_q)` some `g, g' ∈ bosL` move `b` into `dc`
and `a` into `s1` of the image. -/
def meetsR (bosL dc : List (Fin 24)) (s1 : Fin 24 → List (Fin 24)) : Bool :=
  (List.finRange 24).all fun a => (List.finRange 24).all fun b =>
    bosL.any fun g => bosL.any fun g' =>
      dc.contains (mulTab (mulTab g b) g') &&
        (s1 (mulTab (mulTab g b) g')).contains (mulTab (mulTab g a) g')

/-- The tree grid as a predicate on tuples. -/
def gridR (dc : List (Fin 24)) (s1 : Fin 24 → List (Fin 24)) (t : Tup (Fin 3)) : Prop :=
  permEquiv.symm t.2 ∈ dc ∧ permEquiv.symm (t.1 2) ∈ s1 (permEquiv.symm t.2)

theorem meetsR_sound {f : Fam} {bosL dc : List (Fin 24)} {s1 : Fin 24 → List (Fin 24)}
    (hbos : ∀ g ∈ bosL, permTab g ∈ bos f) (h : meetsR bosL dc s1 = true) (t : Tup (Fin 3)) :
    ∃ q : PF f, gridR dc s1 (actF q.1 t) := by
  set a := permEquiv.symm (t.1 2)
  set b := permEquiv.symm t.2
  have ha : t.1 2 = permTab a := (permEquiv.apply_symm_apply _).symm
  have hb : t.2 = permTab b := (permEquiv.apply_symm_apply _).symm
  simp only [meetsR, List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
    Bool.and_eq_true, List.contains_iff_mem] at h
  obtain ⟨g, hg, g', hg', hdc, hs1⟩ := h a b
  refine ⟨⟨(1, false, permTab g, permTab g'), hbos g hg, hbos g' hg'⟩, ?_⟩
  have e : ∀ c : Fin 24, permEquiv.symm (permTab (mulTab (mulTab g c) g')) = mulTab (mulTab g c) g' :=
    fun c => permEquiv.symm_apply_apply _
  simp only [gridR, actF_apply, eInv, Bool.false_eq_true, if_false, Equiv.Perm.coe_one, id]
  rw [ha, hb, ← permTab_mulTab, ← permTab_mulTab, ← permTab_mulTab, ← permTab_mulTab]
  show permEquiv.symm (permEquiv _) ∈ dc ∧
    permEquiv.symm (permEquiv _) ∈ s1 (permEquiv.symm (permEquiv _))
  simp only [Equiv.symm_apply_apply]
  exact ⟨hdc, hs1⟩

/-! ### The verifier's grids (`route2.tree_grid`) -/

/-- `BOS` of families 31 and 13 (`S{0,1,2}`) and of 22 (`S{0,1} × S{2,3}`), as indices. -/
def bos31L : List (Fin 24) := [0, 2, 6, 8, 12, 14]
def bos22L : List (Fin 24) := [0, 1, 6, 7]

theorem bos31L_mem : ∀ g ∈ bos31L, permTab g ∈ bos .f31 := by decide
theorem bos13L_mem : ∀ g ∈ bos31L, permTab g ∈ bos .f13 := by decide
theorem bos22L_mem : ∀ g ∈ bos22L, permTab g ∈ bos .f22 := by decide

def dc31 : List (Fin 24) := [0, 1]
def s1_31 : Fin 24 → List (Fin 24) := fun d =>
  if d = 0 then [0, 1, 2, 3, 7, 8, 9] else [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17]

def dc22 : List (Fin 24) := [0, 2, 16]
def s1_22 : Fin 24 → List (Fin 24) := fun d =>
  if d = 0 then [0, 1, 2, 3, 6, 7, 8, 9, 16, 17]
  else if d = 16 then [0, 1, 2, 3, 4, 5, 16, 17, 22, 23]
  else List.finRange 24

theorem meetsR_31 : meetsR bos31L dc31 s1_31 = true := by decide
theorem meetsR_22 : meetsR bos22L dc22 s1_22 = true := by decide

end LayerDProto

#print axioms LayerDProto.actF_mul
#print axioms LayerDProto.mulPF_bijective
#print axioms LayerDProto.sum_mul_eq_zero_of_symF
#print axioms LayerDProto.tupEquiv_actIdx
#print axioms LayerDProto.meetsR_sound
#print axioms LayerDProto.meetsR_31
#print axioms LayerDProto.meetsR_22
