import LayerDProto.R2AsmKernel
import LayerDProto.R2Coset

/-!
# Layer D, (E′): the per-family assembly

From the kernel-checked chunk values `partD … = some L`, the per-part checks (`partStaticOK`, `partAtDOK`)
and the per-grid-value check `familyAtDOK`:

* `family_at_d`: at every grid point `t = (t₀, t₁, S1[i₂], d)`, `Sym_H D(t)` equals the claimed digit
  `v[(t₀ · 24 + t₁) |S1| + i₂]`, where `D = ∑_parts fac · F_part`;
* `family_zero`: if the claimed digits are zero at every grid value of a tree grid that meets every orbit,
  then `∑_t D(t) x_t = 0` for the coefficients `x` of layer C's `twirl_rep`.

Nothing here assumes the `Gᵀπ` form of the tables: a part's tables are any integer matrices.
-/

open Finset WernerEndpoint

namespace LayerDProto

/-! ## Small facts -/

theorem partD_ok (β w bnd : ℕ) (ks : List ℕ) (k : ℕ) (X Bl Br : List (List ℤ)) (fac : ℤ)
    (rhos : List (List (List (List ℤ)))) (d : ℕ) (S1 : List ℕ) (gs : List MGroup) (v : ℤ)
    (h : partD β w bnd ks k X Bl Br fac rhos d S1 gs = some v) :
    partOK w bnd ks k X Bl Br rhos d S1 gs = true := by
  unfold partD at h
  split at h
  · exact absurd h (by simp)
  · rename_i hb
    have : (groupOK d gs && partOK w bnd ks k X Bl Br rhos d S1 gs) = true := by simpa using hb
    rw [Bool.and_eq_true] at this
    exact this.2

theorem foldl_add_sum_nat (l : List ℕ) (a : ℕ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

theorem list_eq_of_length4 (l : List ℕ) (h : l.length = 4) : l = [nth l 0 1, nth l 1 1, nth l 2 1, nth l 3 1] := by
  match l, h with
  | [a, b, c, e], _ => rfl

theorem sum_list_comm {α β : Type*} (s : Finset α) (l : List β) (g : α → β → ℤ) :
    ∑ a ∈ s, (l.map (g a)).sum = (l.map fun b => ∑ a ∈ s, g a b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [sum_add_distrib, ih]

theorem flatMap_sum {α : Type*} (l : List α) (f : α → List ℤ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem repsOf_sum (gs : List MGroup) (g : KPar → ℤ) :
    (gs.map fun mg => (mg.2.map fun sg => (sg.2.map g).sum).sum).sum = ((repsOf gs).map g).sum := by
  simp [repsOf, List.map_flatMap, flatMap_sum]

theorem rhoE_le (rhos : List (List (List (List ℤ)))) (f s c e : ℕ) :
    |rhoE rhos f s c e| ≤ (tabMax rhos f : ℤ) := by
  unfold rhoE
  refine (ent_le_entMax _ c e).trans ?_
  by_cases hs : s < (rhos.getD f []).length
  · rw [List.getD_eq_getElem _ [] hs]
    have : (rhos.getD f [])[s] ∈ nth rhos f [] := by rw [nth_eq_getD]; exact List.getElem_mem _
    exact_mod_cast le_maxNat _ _ (List.mem_map.mpr ⟨_, this, rfl⟩)
  · rw [List.getD_eq_default _ _ (not_lt.mp hs)]
    simp [entMax, maxNat]

/-- **The digit bound of one part.** -/
theorem Fv_bound (k0 k1 k2 kq k : ℕ) (rhos : List (List (List (List ℤ)))) (X Bl Br : List (List ℤ))
    (hBl : ∀ r ∈ Bl, r.length = k) (hBr : ∀ r ∈ Br, r.length = k) (s0 s1 s2 s3 : ℕ) :
    |Fv k0 k1 k2 kq rhos (Ymat k X Bl Br) s0 s1 s2 s3| ≤
      (((k0 * k1 * k2 * kq) * (k0 * k1 * k2 * kq) * (rowSumMax Bl * entMax X * rowSumMax Br) *
        (tabMax rhos 0 * tabMax rhos 1 * tabMax rhos 2 * tabMax rhos 3) : ℕ) : ℤ) := by
  rw [Fv_eq_Fd]
  unfold Fd
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ x ∈ P4 k0 k1 k2 kq, |rhoE rhos 0 s0 x.1.1.1 x.1.1.2 * rhoE rhos 1 s1 x.1.2.1.1 x.1.2.1.2 *
      rhoE rhos 2 s2 x.1.2.2.1 x.1.2.2.2 * rhoE rhos 3 s3 x.2.1 x.2.2 *
      Ymat k X Bl Br (enc4 k1 k2 kq (cOf x)) (enc4 k1 k2 kq (eOf x))| ≤
      ((tabMax rhos 0 * tabMax rhos 1 * tabMax rhos 2 * tabMax rhos 3 : ℕ) : ℤ) *
        ((rowSumMax Bl * entMax X * rowSumMax Br : ℕ) : ℤ) := by
    intro x _
    simp only [abs_mul, Nat.cast_mul]
    gcongr
    · exact rhoE_le _ _ _ _ _
    · exact rhoE_le _ _ _ _ _
    · exact rhoE_le _ _ _ _ _
    · exact rhoE_le _ _ _ _ _
    · exact Ymat_bound k X Bl Br hBl hBr _ _
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hc : (P4 k0 k1 k2 kq).card = (k0 * k1 * k2 * kq) * (k0 * k1 * k2 * kq) := by
    simp [P4, box, sq, card_product]; ring
  rw [hc]
  push_cast
  ring_nf
  exact le_refl _

theorem pk_append (b : ℕ) (l1 l2 : List ℤ) : pk b (l1 ++ l2) = pk b l1 + pow2 (b * l1.length) * pk b l2 := by
  induction l1 with
  | nil => simp [pk, pow2]
  | cons x xs ih =>
    simp only [List.cons_append, pk, ih, List.length_cons, pow2_eq]
    rw [Nat.mul_succ, pow_add]
    ring

theorem pkB_eq (b : ℕ) : ∀ (f : ℕ) (l : List ℤ), pkB b f l = pk b l
  | 0, l => rfl
  | f + 1, l => by
    unfold pkB
    split
    · rfl
    · rw [pkB_eq b f, pkB_eq b f]
      conv_rhs => rw [← List.take_append_drop (l.length / 2) l]
      rw [pk_append, List.length_take, min_eq_left (Nat.div_le_self _ _)]

/-! ## A part's functional and the grid points -/

/-- A part's functional on tuples (without `fac`). -/
noncomputable def FTP (P : PartData) (t : Tup (Fin 3)) : ℤ :=
  FT (nth P.ks 0 1) (nth P.ks 1 1) (nth P.ks 2 1) (nth P.ks 3 1) P.rhos (Ymat P.k P.X P.Bl P.Br) t

/-- The grid point `(t₀, t₁, S1[i₂], d)`. -/
noncomputable def gpt (S1 : List ℕ) (d t0 t1 i2 : ℕ) : Tup (Fin 3) :=
  tupEquiv (![fin24 t0, fin24 t1, fin24 (S1.getD i2 0)], fin24 d)

theorem FTP_bound (P : PartData) (hBl : ∀ r ∈ P.Bl, r.length = P.k)
    (hBr : ∀ r ∈ P.Br, r.length = P.k) (t : Tup (Fin 3)) : |FTP P t| ≤ (Fbound P : ℤ) := by
  unfold FTP FT FI Fbound
  exact Fv_bound _ _ _ _ _ _ _ _ _ hBl hBr _ _ _ _

/-- `repVal` at the representative `p` is the packed grid values of `F ∘ p`. -/
theorem repVal_eq (P : PartData) (k0 k1 k2 kq : ℕ) (hks : P.ks = [k0, k1, k2, kq]) (β : ℕ) (S1 : List ℕ)
    (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24) (p : KPar) (hp : p.ok) (hσ : p.1 ∈ perms3) :
    repVal β k0 k1 k2 kq P.rhos (Ymat P.k P.X P.Bl P.Br) S1 d p =
      ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
        FTP P (actF (toH p) (gpt S1 d t0 t1 i2)) * 2 ^ (β * (i2 + S1.length * (t1 + 24 * t0))) := by
  unfold repVal
  refine sum_congr rfl fun t0 ht0 => sum_congr rfl fun t1 ht1 => sum_congr rfl fun i2 hi2 => ?_
  congr 1
  have hx : S1.getD i2 0 < 24 := by
    rw [List.getD_eq_getElem _ _ (mem_range.mp hi2)]; exact hS1 _ (List.getElem_mem _)
  unfold FTP FT gpt
  rw [toH, ← tupEquiv_actIdx, Equiv.symm_apply_apply, FI_actIdx _ _ _ _ _ _ p hp hσ, hks]
  simp only [nth, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, fin24, Nat.mod_eq_of_lt (mem_range.mp ht0), Nat.mod_eq_of_lt (mem_range.mp ht1),
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hd]

/-! ## One part -/

theorem list_sum_range {α : Type*} (l : List α) (h : α → ℤ) (d : α) :
    (l.map h).sum = ∑ j ∈ range l.length, h (l.getD j d) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

theorem partStaticOK_spec (bosL : List ℕ) (P : PartData) (h : partStaticOK bosL P = true) :
    P.ks = [nth P.ks 0 1, nth P.ks 1 1, nth P.ks 2 1, nth P.ks 3 1] ∧ (∀ r ∈ P.Bl, r.length = P.k) ∧
      (∀ r ∈ P.Br, r.length = P.k) ∧ closureOK bosL (P.folds.map (·.κ)) P.Ks P.tree = true ∧
      ∀ fd ∈ P.folds, foldDatumOK P fd = true := by
  simp only [partStaticOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hl, hBl⟩, hBr⟩, hc⟩, hf⟩ := h
  exact ⟨list_eq_of_length4 _ hl, hBl, hBr, hc, hf⟩

theorem cosetOKz_cosetOK (bosL : List ℕ) (Ks reps : List KPar) (dec : List (ℕ × ℕ))
    (h : cosetOKz bosL Ks reps dec = true) : cosetOK bosL Ks reps dec = true := by
  simp only [cosetOKz, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hc⟩, hr⟩, hz⟩ := h
  simp only [cosetOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨hl, hc⟩, hr⟩, fun i hi => ?_⟩
  have hi' : i < ((hcodes bosL).zip dec).length := by simp only [List.length_zip, hl, min_self]; rw [← hl]; exact hi
  have hm := hz _ (List.getElem_mem hi')
  simp only [List.getElem_zip] at hm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hm
  rw [nth_eq_getD dec, List.getD_eq_getElem _ _ hi, nth_eq_getD (hcodes bosL),
    List.getD_eq_getElem _ _ (by rw [← hl]; exact hi)]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem partAtDOK_spec (bosL : List ℕ) (P : PartData) (Q : PartAtD) (h : partAtDOK bosL P Q = true) :
    cosetOK bosL P.Ks Q.reps Q.dec = true ∧ Q.chunks.flatMap (fun c => repsOf c.1) = Q.reps := by
  simp only [partAtDOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨cosetOKz_cosetOK _ _ _ _ h.1, h.2⟩

/-- **`Sym_H` of one part** is `|K|` times the sum over the coset representatives. -/
theorem part_sym {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (P : PartData) (Q : PartAtD) (hstat : partStaticOK bosL P = true) (hat : partAtDOK bosL P Q = true)
    (t : Tup (Fin 3)) :
    ∑ p : PF f, FTP P (actF p.1 t) =
      (P.Ks.length : ℤ) * ∑ j ∈ range Q.reps.length, FTP P (actF (toH (Q.reps.getD j ([], false, 0, 0))) t) := by
  obtain ⟨hks, -, -, hclos, hfold⟩ := partStaticOK_spec bosL P hstat
  obtain ⟨hcos, -⟩ := partAtDOK_spec bosL P Q hat
  have hb24 : ∀ c ∈ bosL, c < 24 := fun c hc => (hbos c hc).1
  have hg : ∀ g ∈ P.folds.map (·.κ), InvT (FTP P) (toH g) := by
    intro g hg t'
    obtain ⟨fd, hfd, rfl⟩ := List.mem_map.mp hg
    have h := hfold fd hfd
    simp only [foldDatumOK, Bool.and_eq_true] at h
    obtain ⟨htab, hB⟩ := h
    rw [hks] at htab hB
    exact FT_actF_toH fd.w _ _ _ _ P.k P.rhos P.X P.Bl P.Br fd.κ fd.τ fd.As fd.Cs fd.als fd.Q fd.R
      htab hB t'
  have hinvK := closure_inv (FTP P) bosL hb24 _ P.Ks P.tree hclos hg
  have hKs : ∀ κ ∈ P.Ks, parIn bosL κ = true := by
    simp only [closureOK, Bool.and_eq_true, List.all_eq_true] at hclos
    exact hclos.1.1.2
  exact sum_coset bosL hbos hcomp hnd P.Ks Q.reps Q.dec hcos hKs (fun h => FTP P (actF h t))
    (fun κ hκ r => by simp only; rw [← actF_mul]; exact hinvK κ hκ _)

/-- **The chunks of one part at one grid value** pack the grid values of `∑_{r ∈ reps} F ∘ r`. -/
theorem part_packed (bosL : List ℕ) (hb24 : ∀ c ∈ bosL, c < 24) (P : PartData) (Q : PartAtD)
    (hstat : partStaticOK bosL P = true) (hat : partAtDOK bosL P Q = true) (β : ℕ) (S1 : List ℕ)
    (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24)
    (hD : ∀ c ∈ Q.chunks, partD β P.w P.bnd P.ks P.k P.X P.Bl P.Br P.fac P.rhos d S1 c.1 = some c.2) :
    (Q.chunks.map (·.2)).sum = P.fac * ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
      (∑ j ∈ range Q.reps.length, FTP P (actF (toH (Q.reps.getD j ([], false, 0, 0))) (gpt S1 d t0 t1 i2))) *
        2 ^ (β * (i2 + S1.length * (t1 + 24 * t0))) := by
  obtain ⟨hks, -, -, -, -⟩ := partStaticOK_spec bosL P hstat
  obtain ⟨hcos, hflat⟩ := partAtDOK_spec bosL P Q hat
  obtain ⟨-, -, hreps, -⟩ := cosetOK_spec bosL P.Ks Q.reps Q.dec hcos
  set rv : KPar → ℤ := fun r => ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
    FTP P (actF (toH r) (gpt S1 d t0 t1 i2)) * 2 ^ (β * (i2 + S1.length * (t1 + 24 * t0))) with hrv
  have hok : ∀ r, parIn bosL r = true → r.ok ∧ r.1 ∈ perms3 := fun r hr => by
    obtain ⟨a, b, c⟩ := parIn_spec bosL r hr
    exact ⟨⟨hb24 _ b, hb24 _ c⟩, a⟩
  have hc : ∀ c ∈ Q.chunks, c.2 = P.fac * ((repsOf c.1).map rv).sum := by
    intro c hcm
    have hp := hD c hcm
    obtain ⟨k0, k1, k2, kq, hks', -, hv⟩ := partD_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp
    rw [hv, repsOf_sum]
    congr 1
    have hmem : ∀ r ∈ repsOf c.1, r ∈ Q.reps := fun r hr => by
      rw [← hflat]; exact List.mem_flatMap.mpr ⟨c, hcm, hr⟩
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    obtain ⟨h1, h2⟩ := hok r (hreps r (hmem r hr))
    exact repVal_eq P k0 k1 k2 kq hks' β S1 hS1 d hd r h1 h2
  rw [List.map_congr_left hc, List.sum_map_mul_left]
  rw [show (Q.chunks.map fun c => ((repsOf c.1).map rv).sum).sum = (Q.reps.map rv).sum by
    rw [← hflat, List.map_flatMap, flatMap_sum]]
  congr 1
  rw [list_sum_range Q.reps rv ([], false, 0, 0), sum_comm]
  refine sum_congr rfl fun t0 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun t1 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i2 _ => ?_
  rw [sum_mul]

/-! ## One family at one grid value -/

theorem abs_list_sum_le {α : Type*} (l : List α) (g h : α → ℤ) (hgh : ∀ x ∈ l, |g x| ≤ h x) :
    |(l.map g).sum| ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (hgh a (by simp)) (ih fun x hx => hgh x (by simp [hx])))

/-- Triple sums over the grid of one grid value as one packed sum. -/
theorem grid_sum_eq (s β : ℕ) (g : ℕ → ℕ → ℕ → ℤ) :
    ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range s, g t0 t1 i2 * 2 ^ (β * (i2 + s * (t1 + 24 * t0))) =
      ∑ j ∈ range (24 * 24 * s), g (j / (24 * s)) (j / s % 24) (j % s) * 2 ^ (β * j) := by
  rw [sum_range_blocks _ s (24 * 24), sum_range_blocks _ 24 24]
  refine sum_congr rfl fun t0 _ => sum_congr rfl fun t1 ht1 => sum_congr rfl fun i2 hi2 => ?_
  obtain ⟨d0, d1, d2⟩ := enc3_digits (k1 := 24) (k2 := s) (a0 := t0) (mem_range.mp ht1) (mem_range.mp hi2)
  simp only [enc3] at d0 d1 d2
  rw [d0, d1, d2]
  congr 2
  ring

/-- **The assembly at one grid value.** At every grid point `(t₀, t₁, S1[i₂], d)`, `Sym_H` of the family's
functional `D = ∑_parts fac · F_part` is the claimed digit. -/
theorem family_at_d {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (β : ℕ) (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24)
    (parts : List (PartData × PartAtD)) (v : List ℤ) (vb : ℕ)
    (hstat : ∀ x ∈ parts, partStaticOK bosL x.1 = true) (hat : ∀ x ∈ parts, partAtDOK bosL x.1 x.2 = true)
    (hD : ∀ x ∈ parts, ∀ c ∈ x.2.chunks,
      partD β x.1.w x.1.bnd x.1.ks x.1.k x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos d S1 c.1 = some c.2)
    (hfam : familyAtDOK β S1 parts v vb = true) :
    ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < S1.length,
      ∑ p : PF f, (parts.map fun x => x.1.fac * FTP x.1 (actF p.1 (gpt S1 d t0 t1 i2))).sum =
        v.getD ((t0 * 24 + t1) * S1.length + i2) 0 := by
  simp only [familyAtDOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfam
  obtain ⟨⟨⟨⟨hvl, hpk⟩, hvb⟩, hvb4⟩, hB4⟩ := hfam
  have hb24 : ∀ c ∈ bosL, c < 24 := fun c hc => (hbos c hc).1
  set s := S1.length
  set SD : Tup (Fin 3) → ℤ := fun t => ∑ p : PF f, (parts.map fun x => x.1.fac * FTP x.1 (actF p.1 t)).sum with hSD
  set SymP : PartData → Tup (Fin 3) → ℤ := fun P t => ∑ p : PF f, FTP P (actF p.1 t) with hSymP
  have hSDP : ∀ t, SD t = (parts.map fun x => x.1.fac * SymP x.1 t).sum := fun t => by
    simp only [hSD, hSymP]
    rw [sum_list_comm]
    exact congrArg List.sum (List.map_congr_left fun x _ => (mul_sum _ _ _).symm)
  -- each part: `|K| ∑ L = fac ∑_grid Sym F 2^(β pos)`
  have hpart : ∀ x ∈ parts, (x.1.Ks.length : ℤ) * (x.2.chunks.map (·.2)).sum =
      x.1.fac * ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range s,
        SymP x.1 (gpt S1 d t0 t1 i2) * 2 ^ (β * (i2 + s * (t1 + 24 * t0))) := by
    intro x hx
    rw [part_packed bosL hb24 x.1 x.2 (hstat x hx) (hat x hx) β S1 hS1 d hd (hD x hx), mul_left_comm]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun t0 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun t1 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i2 _ => ?_
    rw [hSymP]
    simp only
    rw [part_sym bosL hbos hcomp hnd x.1 x.2 (hstat x hx) (hat x hx)]
    ring
  -- the family total
  have htot : famTotal parts = ∑ j ∈ range (24 * 24 * s),
      SD (gpt S1 d (j / (24 * s)) (j / s % 24) (j % s)) * 2 ^ (β * j) := by
    rw [← grid_sum_eq s β (fun t0 t1 i2 => SD (gpt S1 d t0 t1 i2))]
    unfold famTotal
    rw [foldl_add_sum, zero_add]
    have e : (parts.map fun x => (x.1.Ks.length : ℤ) * (x.2.chunks.map (·.2)).foldl (· + ·) 0) =
        parts.map fun x => x.1.fac * ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range s,
          SymP x.1 (gpt S1 d t0 t1 i2) * 2 ^ (β * (i2 + s * (t1 + 24 * t0))) :=
      List.map_congr_left fun x hx => by rw [foldl_add_sum, zero_add]; exact hpart x hx
    rw [e]
    simp only [mul_sum]
    rw [← sum_list_comm]
    refine sum_congr rfl fun t0 _ => ?_
    rw [← sum_list_comm]
    refine sum_congr rfl fun t1 _ => ?_
    rw [← sum_list_comm]
    refine sum_congr rfl fun i2 _ => ?_
    rw [hSDP, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun x _ => by ring)
  -- the bound of the true digits
  have hSDb : ∀ t, |SD t| ≤ (famBound parts : ℤ) := by
    intro t
    rw [hSDP]
    unfold famBound
    rw [foldl_add_sum_nat, zero_add, Nat.cast_list_sum, List.map_map]
    refine abs_list_sum_le _ _ _ fun x hx => ?_
    obtain ⟨-, hBl, hBr, -, -⟩ := partStaticOK_spec bosL x.1 (hstat x hx)
    simp only [Function.comp, hSymP]
    rw [part_sym bosL hbos hcomp hnd x.1 x.2 (hstat x hx) (hat x hx), abs_mul, abs_mul]
    push_cast
    rw [Int.abs_eq_natAbs x.1.fac, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc, mul_assoc]
    gcongr
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun j _ => FTP_bound x.1 hBl hBr _).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
  -- the digits
  have hpk' : famTotal parts = ∑ j ∈ range (24 * 24 * s), v.getD j 0 * 2 ^ (β * j) := by
    rw [← hpk, pkB_eq, pk_eq, hvl]
  have hdig := digits_of_eq β (24 * 24 * s) (fun j => SD (gpt S1 d (j / (24 * s)) (j / s % 24) (j % s)))
    (fun j => v.getD j 0) (famBound parts) vb (fun j _ => hSDb _) (fun j _ => boundedBy_spec vb v hvb j)
    hB4 hvb4 (htot.symm.trans hpk')
  intro t0 ht0 t1 ht1 i2 hi2
  have hj : (t0 * 24 + t1) * s + i2 < 24 * 24 * s := by
    have := enc3_lt (k0 := 24) (k1 := 24) (k2 := s) ht0 ht1 hi2
    simp only [enc3] at this; linarith
  have := hdig _ hj
  obtain ⟨d0, d1, d2⟩ := enc3_digits (k1 := 24) (k2 := s) (a0 := t0) ht1 hi2
  simp only [enc3] at d0 d1 d2
  simp only [d0, d1, d2] at this
  exact this

theorem familyZeroOK_spec (β : ℕ) (S1 : List ℕ) (parts : List (PartData × PartAtD))
    (h : familyZeroOK β parts = true) :
    familyAtDOK β S1 parts (List.replicate (24 * 24 * S1.length) 0) 0 = true := by
  simp only [familyZeroOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hz : ∀ j, (List.replicate (24 * 24 * S1.length) (0 : ℤ)).getD j 0 = 0 := fun j => by
    rw [List.getD_eq_getElem?_getD]; cases h : (List.replicate (24 * 24 * S1.length) (0 : ℤ))[j]? <;>
      simp_all [List.getElem?_replicate]
  simp only [familyAtDOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_replicate]
  refine ⟨⟨⟨⟨trivial, ?_⟩, ?_⟩, by positivity⟩, h.2⟩
  · rw [pkB_eq, pk_eq, h.1]
    exact sum_eq_zero fun j _ => by rw [hz, zero_mul]
  · simp [boundedBy, List.all_replicate]

/-- `family_at_d` with zero claimed digits, for the parts `Ps` (with their data `Qs` at this grid value). -/
theorem family_at_d_zero {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (β : ℕ) (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24)
    (Ps : List PartData) (Qs : List PartAtD) (hlen : Ps.length = Qs.length) (vb : ℕ)
    (hstat : ∀ x ∈ Ps.zip Qs, partStaticOK bosL x.1 = true) (hat : ∀ x ∈ Ps.zip Qs, partAtDOK bosL x.1 x.2 = true)
    (hD : ∀ x ∈ Ps.zip Qs, ∀ c ∈ x.2.chunks,
      partD β x.1.w x.1.bnd x.1.ks x.1.k x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos d S1 c.1 = some c.2)
    (hfam : familyAtDOK β S1 (Ps.zip Qs) (List.replicate (24 * 24 * S1.length) 0) vb = true) :
    ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < S1.length,
      ∑ p : PF f, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt S1 d t0 t1 i2))).sum = 0 := by
  intro t0 ht0 t1 ht1 i2 hi2
  have h := family_at_d bosL hbos hcomp hnd β S1 hS1 d hd (Ps.zip Qs) _ vb hstat hat hD hfam t0 ht0 t1 ht1 i2 hi2
  have hz : ∀ j, (List.replicate (24 * 24 * S1.length) (0 : ℤ)).getD j 0 = 0 := fun j => by
    rw [List.getD_eq_getElem?_getD]; cases h : (List.replicate (24 * 24 * S1.length) (0 : ℤ))[j]? <;>
      simp_all [List.getElem?_replicate]
  rw [hz] at h
  rw [← h]
  refine sum_congr rfl fun p _ => ?_
  have e : (Ps.zip Qs).map Prod.fst = Ps := List.map_fst_zip (le_of_eq hlen)
  conv_lhs => rw [← e]
  rw [List.map_map]
  rfl

/-- **The identity on the twirl.** If `Sym_H D` vanishes at every point of a tree grid that meets every
orbit (each grid value given by `family_at_d_zero`), then `∑_t D(t) x_t = 0` for the coefficients `x` of
layer C's `twirl_rep`. -/
theorem family_zero {f : Fam} (Ps : List PartData) {x : Tup (Fin 3) → ℝ}
    (hs : ∀ π t, x (sitePermT π t) = x t) (hi : ∀ t, x (invT t) = x t)
    (hl : ∀ g ∈ bos f, ∀ t, x (lmulT g t) = x t) (hr : ∀ g ∈ bos f, ∀ t, x (rmulT g t) = x t)
    (bosF dc : List (Fin 24)) (s1 : Fin 24 → List (Fin 24)) (hbosF : ∀ g ∈ bosF, permTab g ∈ bos f)
    (hmeets : meetsR bosF dc s1 = true)
    (hzero : ∀ dd ∈ dc, ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < (s1 dd).length,
      ∑ p : PF f, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt ((s1 dd).map Fin.val) dd t0 t1 i2))).sum = 0) :
    ∑ t, ((Ps.map fun P => P.fac * FTP P t).sum : ℂ) * (x t : ℂ) = 0 := by
  refine sum_mul_eq_zero_of_symF (fun t => ((Ps.map fun P => P.fac * FTP P t).sum : ℂ)) hs hi hl hr
    (gridR dc s1) (meetsR_sound hbosF hmeets) fun t ht => ?_
  set ti := tupEquiv.symm t with hti
  have htt : t = tupEquiv ti := (Equiv.apply_symm_apply _ _).symm
  have h1 : ti.2 = permEquiv.symm t.2 := rfl
  have h2 : ti.1 2 = permEquiv.symm (t.1 2) := rfl
  obtain ⟨hdc, hs1⟩ := ht
  rw [← h1, ← h2] at hs1
  rw [← h1] at hdc
  obtain ⟨i2, hi2, hi2e⟩ := List.getElem_of_mem hs1
  have hg : gpt ((s1 ti.2).map Fin.val) ti.2 (ti.1 0) (ti.1 1) i2 = t := by
    rw [htt, gpt]
    congr 1
    have hf : ∀ a : Fin 24, fin24 a = a := fun a => fin24_of_lt _ a.isLt
    have hg2 : ((s1 ti.2).map Fin.val).getD i2 0 = ti.1 2 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi2), List.getElem_map, hi2e]
    refine Prod.ext ?_ (hf _)
    funext i
    fin_cases i
    · exact hf _
    · exact hf _
    · show fin24 (((s1 ti.2).map Fin.val).getD i2 0) = ti.1 2
      rw [hg2, hf]
  have := hzero ti.2 hdc (ti.1 0) (ti.1 0).isLt (ti.1 1) (ti.1 1).isLt i2 (by simpa using hi2)
  rw [hg] at this
  simp only
  exact_mod_cast this

end LayerDProto
#print axioms LayerDProto.family_at_d
#print axioms LayerDProto.family_at_d_zero
#print axioms LayerDProto.family_zero
#print axioms LayerDProto.familyZeroOK_spec
