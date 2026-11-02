import LayerDProto.R2FoldB

/-!
# Layer D, (E′): parameters as group elements, `K`-invariance on tuples, closure under products

The kernel's parameters `κ = ([σ 0, σ 1, σ 2], ε, g, g')` (`KPar`, indices) are elements `toH κ` of the
parametrized group of `SymWerner.lean` (`HPar`, acting by `actF`). This file proves:

* `actF_toH`: `actF (toH κ)` acts on index tuples as `kact` does (`(κ · t)_f = r_s(t_{σ f})`);
* `FT_actF_toH`: for a part's functional `FT` on tuples, the fold checks for `κ` give
  `FT ∘ actF (toH κ) = FT` (`fold_invariant` transported to tuples);
* `inv_mulP`: invariance is closed under the composition `mulP` (so invariance under checked generators
  gives invariance under every product of them).
-/

open Finset WernerEndpoint

set_option profiler true
set_option profiler.threshold 2000

namespace LayerDProto

/-! ## Site permutations from lists -/

/-- The permutation of `Fin 3` with `i ↦ l[i]` for the six lists of `perms3` (identity otherwise). -/
def perm3 (l : List ℕ) : Equiv.Perm (Fin 3) :=
  if l = [0, 2, 1] then Equiv.swap 1 2
  else if l = [1, 0, 2] then Equiv.swap 0 1
  else if l = [1, 2, 0] then finRotate 3
  else if l = [2, 0, 1] then (finRotate 3)⁻¹
  else if l = [2, 1, 0] then Equiv.swap 0 2
  else 1

theorem perm3_apply (l : List ℕ) (hl : l ∈ perms3) (i : Fin 3) : ((perm3 l i : Fin 3) : ℕ) = nth l i 0 := by
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;> decide

/-- `a mod 24` as an index. -/
def fin24 (a : ℕ) : Fin 24 := ⟨a % 24, Nat.mod_lt _ (by norm_num)⟩

theorem fin24_of_lt (a : ℕ) (h : a < 24) : fin24 a = ⟨a, h⟩ := Fin.ext (Nat.mod_eq_of_lt h)

theorem fin24_pmul (a b : ℕ) (ha : a < 24) (hb : b < 24) : fin24 (pmul a b) = mulTab (fin24 a) (fin24 b) := by
  rw [fin24_of_lt a ha, fin24_of_lt b hb]
  have e := pmul_eq ⟨a, ha⟩ ⟨b, hb⟩
  simp only at e
  apply Fin.ext
  show pmul a b % 24 = _
  rw [e, Nat.mod_eq_of_lt (Fin.isLt _)]

theorem pinv_lt (a : ℕ) (ha : a < 24) : pinv a < 24 := by
  have e := pinv_eq ⟨a, ha⟩
  simp only at e
  rw [e]; exact Fin.isLt _

theorem fin24_pinv (a : ℕ) (ha : a < 24) : fin24 (pinv a) = invTab (fin24 a) := by
  rw [fin24_of_lt a ha]
  have e := pinv_eq ⟨a, ha⟩
  simp only at e
  apply Fin.ext
  show pinv a % 24 = _
  rw [e, Nat.mod_eq_of_lt (Fin.isLt _)]

/-- The index form of a kernel parameter. -/
def toI (κ : KPar) : IPar := (perm3 κ.1, κ.2.1, fin24 κ.2.2.1, fin24 κ.2.2.2)

/-- The group element of a kernel parameter. -/
noncomputable def toH (κ : KPar) : HPar := toHPar (toI κ)

theorem actIdx_toI (κ : KPar) (hκ : κ.ok) (hσ : κ.1 ∈ perms3) (ti : (Fin 3 → Fin 24) × Fin 24) :
    (∀ i : Fin 3, (((actIdx (toI κ) ti).1 i : Fin 24) : ℕ) =
      kact κ (nth [(ti.1 0 : ℕ), ti.1 1, ti.1 2] (nth κ.1 i 0) 0)) ∧
    (((actIdx (toI κ) ti).2 : Fin 24) : ℕ) = kact κ ti.2 := by
  obtain ⟨σ, ε, g, g'⟩ := κ
  obtain ⟨hg, hg'⟩ := hκ
  have eg : fin24 g = ⟨g, hg⟩ := fin24_of_lt g hg
  have eg' : fin24 g' = ⟨g', hg'⟩ := fin24_of_lt g' hg'
  refine ⟨fun i => ?_, ?_⟩
  · simp only [actIdx, toI, eg, eg']
    have hidx : nth [(ti.1 0 : ℕ), ti.1 1, ti.1 2] (nth σ i 0) 0 = (ti.1 (perm3 σ i) : ℕ) := by
      rw [← perm3_apply σ hσ i]
      generalize perm3 σ i = j
      fin_cases j <;> rfl
    rw [hidx]
    exact (kact_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ (ti.1 (perm3 σ i))).symm
  · simp only [actIdx, toI, eg, eg']
    exact (kact_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ ti.2).symm

/-! ## A part's functional on tuples -/

/-- `F` on index tuples. -/
def FI (k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ)
    (ti : (Fin 3 → Fin 24) × Fin 24) : ℤ :=
  Fv k0 k1 k2 kq rhos Y (ti.1 0) (ti.1 1) (ti.1 2) ti.2

/-- `F` on tuples of permutations. -/
noncomputable def FT (k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ)
    (t : Tup (Fin 3)) : ℤ :=
  FI k0 k1 k2 kq rhos Y (tupEquiv.symm t)

theorem FI_actIdx (k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ) (κ : KPar)
    (hκ : κ.ok) (hσ : κ.1 ∈ perms3) (ti : (Fin 3 → Fin 24) × Fin 24) :
    FI k0 k1 k2 kq rhos Y (actIdx (toI κ) ti) =
      Fv k0 k1 k2 kq rhos Y (kact κ (nth [(ti.1 0 : ℕ), ti.1 1, ti.1 2] (nth κ.1 0 0) 0))
        (kact κ (nth [(ti.1 0 : ℕ), ti.1 1, ti.1 2] (nth κ.1 1 0) 0))
        (kact κ (nth [(ti.1 0 : ℕ), ti.1 1, ti.1 2] (nth κ.1 2 0) 0)) (kact κ ti.2) := by
  obtain ⟨h1, h2⟩ := actIdx_toI κ hκ hσ ti
  unfold FI
  rw [h1 0, h1 1, h1 2, h2]
  rfl

/-- **`K`-invariance on tuples** from the fold checks of `κ`. -/
theorem FT_actF_toH (w k0 k1 k2 kq k : ℕ) (rhos : List (List (List (List ℤ)))) (X Bl Br : List (List ℤ))
    (κ : KPar) (τ : Bool) (As Cs : List (List (List ℤ))) (als : List ℤ) (Q R : List (List ℤ))
    (htab : foldTabOK [k0, k1, k2, kq] rhos κ τ As Cs als = true)
    (hB : foldBOK w [k0, k1, k2, kq] k X Bl Br κ τ As Cs als Q R = true) (t : Tup (Fin 3)) :
    FT k0 k1 k2 kq rhos (Ymat k X Bl Br) (actF (toH κ) t) = FT k0 k1 k2 kq rhos (Ymat k X Bl Br) t := by
  obtain ⟨-, hσ, hκ, -⟩ := foldTabOK_spec _ rhos κ τ As Cs als htab
  set ti := tupEquiv.symm t
  have ht : t = tupEquiv ti := (Equiv.apply_symm_apply _ _).symm
  unfold FT
  rw [ht, toH, ← tupEquiv_actIdx, Equiv.symm_apply_apply, Equiv.symm_apply_apply, FI_actIdx _ _ _ _ _ _ κ hκ hσ]
  exact fold_invariant w k0 k1 k2 kq k rhos X Bl Br κ τ As Cs als Q R htab hB _ _ _ _
    (ti.1 0).isLt (ti.1 1).isLt (ti.1 2).isLt ti.2.isLt

/-! ## Closure under products -/

/-- Invariance under a group element. -/
def InvT {β : Type*} (F : Tup (Fin 3) → β) (p : HPar) : Prop := ∀ t, F (actF p t) = F t

theorem invT_one {β : Type*} (F : Tup (Fin 3) → β) : InvT F (1, false, 1, 1) := by
  intro t
  rw [actF_apply]
  simp [eInv]

theorem invT_mulP {β : Type*} (F : Tup (Fin 3) → β) (p q : HPar) (hp : InvT F p) (hq : InvT F q) :
    InvT F (mulP p q) := by
  intro t
  rw [← actF_mul, hp, hq]

/-! ## Products of parameters -/

theorem perm3_comp3 (p q : List ℕ) (hp : p ∈ perms3) (hq : q ∈ perms3) :
    perm3 (comp3 q p) = perm3 q * perm3 p := by
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem perm3_inj (p q : List ℕ) (hp : p ∈ perms3) (hq : q ∈ perms3) (h : perm3 p = perm3 q) : p = q := by
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

theorem parIn_spec (bosL : List ℕ) (p : KPar) (h : parIn bosL p = true) :
    p.1 ∈ perms3 ∧ p.2.2.1 ∈ bosL ∧ p.2.2.2 ∈ bosL := by
  simp only [parIn, Bool.and_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem toH_g (κ : KPar) (h : κ.2.2.1 < 24) : (toH κ).2.2.1 = permTab ⟨κ.2.2.1, h⟩ := by
  simp only [toH, toHPar, toI, fin24_of_lt _ h]

theorem toH_g' (κ : KPar) (h : κ.2.2.2 < 24) : (toH κ).2.2.2 = permTab ⟨κ.2.2.2, h⟩ := by
  simp only [toH, toHPar, toI, fin24_of_lt _ h]

theorem toH_mulK (p q : KPar) (hp : p.1 ∈ perms3) (hq : q.1 ∈ perms3) (hpk : p.ok) (hqk : q.ok) :
    toH (mulK p q) = mulP (toH p) (toH q) := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨τ, δ, h, h'⟩ := q
  obtain ⟨hg, hg'⟩ := hpk
  obtain ⟨hh, hh'⟩ := hqk
  simp only [toH, toHPar, toI, mulK, mulP]
  refine Prod.ext (perm3_comp3 σ τ hp hq) (Prod.ext rfl (Prod.ext ?_ ?_))
  · cases ε
    · simp only [Bool.false_eq_true, if_false]
      rw [fin24_pmul g h hg hh, permTab_mulTab]
    · simp only [if_true]
      rw [fin24_pmul g _ hg (pinv_lt h' hh'), fin24_pinv h' hh', permTab_mulTab, permTab_invTab]
  · cases ε
    · simp only [Bool.false_eq_true, if_false]
      rw [fin24_pmul h' g' hh' hg', permTab_mulTab]
    · simp only [if_true]
      rw [fin24_pmul _ g' (pinv_lt h hh) hg', fin24_pinv h hh, permTab_mulTab, permTab_invTab]

theorem toH_inj (p q : KPar) (hp : p.1 ∈ perms3) (hq : q.1 ∈ perms3) (hpk : p.ok) (hqk : q.ok)
    (h : toH p = toH q) : p = q := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨τ, δ, k, k'⟩ := q
  obtain ⟨hg, hg'⟩ := hpk
  obtain ⟨hk, hk'⟩ := hqk
  simp only [toH, toHPar, toI, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e3 := congrArg Fin.val (permTab_inj h3)
  have e4 := congrArg Fin.val (permTab_inj h4)
  simp only [fin24, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hg', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at e3 e4
  rw [perm3_inj σ τ hp hq h1, h2, e3, e4]

theorem toH_one : toH ([0, 1, 2], false, 0, 0) = (1, false, 1, 1) := by
  simp only [toH, toHPar, toI, fin24_of_lt 0 (by norm_num)]
  refine Prod.ext (by decide) (Prod.ext rfl (Prod.ext ?_ ?_)) <;> exact permTab_zero

/-! ## Invariance of `K` from its generators -/

theorem closure_inv {β : Type*} (F : Tup (Fin 3) → β) (bosL : List ℕ) (hbos : ∀ c ∈ bosL, c < 24)
    (gens Ks : List KPar) (tree : List (ℕ × ℕ)) (h : closureOK bosL gens Ks tree = true)
    (hg : ∀ g ∈ gens, InvT F (toH g)) : ∀ κ ∈ Ks, InvT F (toH κ) := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hl, h0, hKs, hgs, ht⟩ := h
  have ok : ∀ κ, parIn bosL κ = true → κ.1 ∈ perms3 ∧ κ.ok := fun κ hk => by
    obtain ⟨a, b, c⟩ := parIn_spec bosL κ hk
    exact ⟨a, hbos _ b, hbos _ c⟩
  have key : ∀ m, m < Ks.length → InvT F (toH (nth Ks m ([], false, 0, 0))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      cases m with
      | zero => rw [h0, toH_one]; exact invT_one F
      | succ m =>
        obtain ⟨hi, hj, he⟩ := ht m (by omega)
        set j := (nth tree m (0, 0)).1
        set i := (nth tree m (0, 0)).2
        have hgm : nth gens j ([], false, 0, 0) ∈ gens := by
          rw [nth_eq_getD, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
        have hKi : nth Ks i ([], false, 0, 0) ∈ Ks := by
          rw [nth_eq_getD, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        obtain ⟨g1, g2⟩ := ok _ (hgs _ hgm)
        obtain ⟨k1, k2⟩ := ok _ (hKs _ hKi)
        rw [he, toH_mulK _ _ g1 k1 g2 k2]
        exact invT_mulP F _ _ (hg _ hgm) (ih i (by omega) (by omega))
  intro κ hκ
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hκ
  have := key m hm
  rwa [nth_eq_getD, List.getD_eq_getElem _ _ hm] at this

/-! ## Right cosets of `K` -/

theorem perm3_surj : ∀ σ : Equiv.Perm (Fin 3),
    [((σ 0 : Fin 3) : ℕ), σ 1, σ 2] ∈ perms3 ∧ perm3 [((σ 0 : Fin 3) : ℕ), σ 1, σ 2] = σ := by
  decide

theorem mem_hcodes (bosL : List ℕ) (c : KPar) : c ∈ hcodes bosL ↔ parIn bosL c = true := by
  obtain ⟨σ, ε, g, g'⟩ := c
  simp only [hcodes, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
    parIn, Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨σ', hσ', ε', hε', g1, hg1, g2, hg2, rfl, rfl, rfl, rfl⟩
    exact ⟨⟨hσ', hg1⟩, hg2⟩
  · rintro ⟨⟨hσ, hg⟩, hg'⟩
    exact ⟨σ, hσ, ε, by cases ε <;> simp, g, hg, g', hg', rfl, rfl, rfl, rfl⟩

theorem cosetOK_spec (bosL : List ℕ) (Ks reps : List KPar) (dec : List (ℕ × ℕ))
    (h : cosetOK bosL Ks reps dec = true) :
    dec.length = (hcodes bosL).length ∧ Ks.length * reps.length = (hcodes bosL).length ∧
      (∀ r ∈ reps, parIn bosL r = true) ∧ ∀ i < dec.length, (dec.getD i (0, 0)).1 < Ks.length ∧
        (dec.getD i (0, 0)).2 < reps.length ∧
        mulK (Ks.getD (dec.getD i (0, 0)).1 ([], false, 0, 0)) (reps.getD (dec.getD i (0, 0)).2 ([], false, 0, 0)) =
          (hcodes bosL).getD i ([], false, 0, 0) := by
  simp only [cosetOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc, nth_eq_getD] at h
  exact h

/-- **The coset decomposition, checked on codes.** If `K` (listed by `Ks`) leaves `G` invariant and
`(κ, r) ↦ κ r` is a bijection `K × reps → H` (`cosetOK`), then `∑_{h ∈ H} G h = |K| ∑_{r ∈ reps} G r`. -/
theorem sum_coset {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (Ks reps : List KPar) (dec : List (ℕ × ℕ)) (hcos : cosetOK bosL Ks reps dec = true)
    (hKs : ∀ κ ∈ Ks, parIn bosL κ = true) (G : HPar → ℤ)
    (hinv : ∀ κ ∈ Ks, ∀ r, G (mulP (toH κ) r) = G r) :
    ∑ p : PF f, G p.1 = (Ks.length : ℤ) * ∑ j ∈ range reps.length, G (toH (reps.getD j ([], false, 0, 0))) := by
  obtain ⟨hdl, hcard, hreps, hdec⟩ := cosetOK_spec bosL Ks reps dec hcos
  set N := (hcodes bosL).length
  set H := hcodes bosL
  have ok : ∀ c, parIn bosL c = true → c.1 ∈ perms3 ∧ c.ok := fun c hc => by
    obtain ⟨a, b, d⟩ := parIn_spec bosL c hc
    exact ⟨a, (hbos _ b).1, (hbos _ d).1⟩
  have memPF : ∀ c, parIn bosL c = true → (toH c).2.2.1 ∈ bos f ∧ (toH c).2.2.2 ∈ bos f := fun c hc => by
    obtain ⟨-, b, d⟩ := parIn_spec bosL c hc
    obtain ⟨hb1, hb2⟩ := hbos _ b
    obtain ⟨hd1, hd2⟩ := hbos _ d
    rw [toH_g c hb1, toH_g' c hd1]
    exact ⟨hb2, hd2⟩
  have hHin : ∀ h : Fin N, parIn bosL (H[h]) = true := fun h => (mem_hcodes bosL _).mp (List.getElem_mem _)
  -- (i) the group, enumerated
  let e : Fin N → PF f := fun h => ⟨toH H[h], memPF _ (hHin h)⟩
  have he : Function.Bijective e := by
    constructor
    · intro h h' heq
      have := congrArg Subtype.val heq
      simp only [e] at this
      obtain ⟨a1, a2⟩ := ok _ (hHin h)
      obtain ⟨b1, b2⟩ := ok _ (hHin h')
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (toH_inj _ _ a1 b1 a2 b2 this))
    · rintro ⟨⟨σ, ε, g, g'⟩, hg, hg'⟩
      obtain ⟨hσ, hσe⟩ := perm3_surj σ
      set c : KPar := ([((σ 0 : Fin 3) : ℕ), σ 1, σ 2], ε, (permEquiv.symm g : ℕ), (permEquiv.symm g' : ℕ))
      have hgc : permTab (permEquiv.symm g) = g := permEquiv.apply_symm_apply g
      have hgc' : permTab (permEquiv.symm g') = g' := permEquiv.apply_symm_apply g'
      have hc : parIn bosL c = true := by
        simp only [parIn, Bool.and_eq_true, List.contains_iff_mem, c]
        exact ⟨⟨hσ, hcomp _ (by rw [hgc]; exact hg)⟩, hcomp _ (by rw [hgc']; exact hg')⟩
      obtain ⟨h, hh, hhc⟩ := List.getElem_of_mem ((mem_hcodes bosL c).mpr hc)
      refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
      show toH H[h] = _
      rw [hhc]
      simp only [toH, toHPar, toI, c, hσe, fin24_of_lt _ (Fin.isLt _)]
      rw [Fin.eta, Fin.eta, hgc, hgc']
  rw [← Equiv.sum_comp (Equiv.ofBijective e he)]
  simp only [Equiv.ofBijective_apply, e]
  -- (ii) the decomposition `H = K · reps`
  have hd : ∀ h : Fin N, (dec.getD h (0, 0)).1 < Ks.length ∧ (dec.getD h (0, 0)).2 < reps.length ∧
      mulK (Ks.getD (dec.getD h (0, 0)).1 ([], false, 0, 0)) (reps.getD (dec.getD h (0, 0)).2 ([], false, 0, 0)) =
        H[h] := fun h => by
    obtain ⟨a, b, c⟩ := hdec h (by rw [hdl]; exact h.isLt)
    exact ⟨a, b, by rw [c, List.getD_eq_getElem _ _ h.isLt]; rfl⟩
  let d : Fin N → Fin Ks.length × Fin reps.length := fun h => (⟨_, (hd h).1⟩, ⟨_, (hd h).2.1⟩)
  have hdb : Function.Bijective d := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun h h' heq => ?_, by simp [Fintype.card_prod, hcard, N]⟩
    simp only [d, Prod.mk.injEq, Fin.mk.injEq] at heq
    have e1 := (hd h).2.2
    have e2 := (hd h').2.2
    rw [heq.1, heq.2] at e1
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (e1.symm.trans e2))
  have hGh : ∀ h : Fin N, G (toH H[h]) = G (toH (reps.getD (d h).2 ([], false, 0, 0))) := fun h => by
    rw [← (hd h).2.2]
    have hKm : Ks.getD (dec.getD h (0, 0)).1 ([], false, 0, 0) ∈ Ks := by
      rw [List.getD_eq_getElem _ _ (hd h).1]; exact List.getElem_mem _
    have hrm : reps.getD (dec.getD h (0, 0)).2 ([], false, 0, 0) ∈ reps := by
      rw [List.getD_eq_getElem _ _ (hd h).2.1]; exact List.getElem_mem _
    obtain ⟨a1, a2⟩ := ok _ (hKs _ hKm)
    obtain ⟨b1, b2⟩ := ok _ (hreps _ hrm)
    rw [toH_mulK _ _ a1 b1 a2 b2, hinv _ hKm]
  simp only [hGh]
  rw [Fintype.sum_bijective d hdb (fun h => G (toH (reps.getD (d h).2 ([], false, 0, 0))))
    (fun x => G (toH (reps.getD x.2 ([], false, 0, 0)))) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => G (toH (reps.getD j ([], false, 0, 0)))) reps.length

end LayerDProto

#print axioms LayerDProto.FT_actF_toH
#print axioms LayerDProto.invT_mulP
#print axioms LayerDProto.closure_inv
#print axioms LayerDProto.sum_coset
