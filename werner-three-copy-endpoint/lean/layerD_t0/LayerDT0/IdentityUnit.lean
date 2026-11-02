import LayerDT0.IdentityAsm

/-!
# Layer D (t = 0): rows and objective as unit parts (first half of the `hdec` bookkeeping)

* **Unit parts** (`unitPart`): `1 × 1` parts with site tables `δ_{·, j_i}` (`dTab`) and qubit table
  `2^{cyc(a · q)}` (`qTab`). `mTr_unit`: `mTr 2 (w, w_q) m = ∑_s m(s) FTP (unitPart _ j a) s` whenever
  `permTab j_i = w_i⁻¹` and `permTab a = w_q`. In trace (m-)coordinates the site Gram matrix is already
  applied, so the site tables are Kronecker deltas, not `d^{cyc}`.
* **Rows** (`RowCode.uterms`, `mRowVal_uterms`) and **the objective** (`objUTerms`, `mObj_uterms`) as
  integer combinations of unit parts (`remTab`, `conjTab` are index tables of `removeSlot` and of
  conjugation by `π_ABB`, checked by `decide +kernel`).

The rest of the bookkeeping (blocks, regrouping, `hdec_of_data`) is in `IdentityDec.lean`.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint LayerDProto

/-! ### Small list lemmas -/

theorem getD_map_range {α : Type*} (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem listSum_range (f : ℕ → ℝ) : ∀ n, ((List.range n).map f).sum = ∑ i : Fin n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range f n, Fin.sum_univ_castSucc]
    simp

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (v : β → ℝ) :
    ((L.flatMap g).map v).sum = (L.map fun a => ((g a).map v).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! ### Index tables -/

/-- The index of `removeSlot (permTab w) r` (verifier convention `swap(r, w r) ∘ w`). -/
def remTab : Fin 24 → Fin 4 → Fin 24 :=
  ![![0, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 0, 2], ![3, 1, 5, 2], ![4, 1, 5, 2], ![5, 0, 5, 0],
    ![0, 0, 6, 6], ![1, 1, 6, 6], ![2, 14, 6, 8], ![3, 15, 11, 8], ![4, 20, 11, 8], ![5, 21, 11, 6],
    ![2, 14, 6, 12], ![3, 15, 19, 12], ![0, 14, 0, 14], ![1, 15, 21, 14], ![5, 14, 5, 14],
    ![4, 15, 11, 12], ![4, 20, 19, 12], ![5, 21, 19, 6], ![1, 20, 21, 14], ![0, 21, 21, 0],
    ![3, 20, 19, 8], ![2, 21, 21, 2]]

/-- The index of `π_ABB · permTab w · π_ABB⁻¹`. -/
def conjTab : Fin 24 → Fin 24 :=
  ![0, 14, 6, 12, 8, 2, 5, 16, 19, 13, 22, 3, 11, 17, 21, 15, 23, 9, 10, 4, 20, 1, 18, 7]

/-- The index of `swap 0 3`. -/
def swIdx : Fin 24 := 21

theorem permTab_remTab : ∀ (w : Fin 24) (r : Fin 4), permTab (remTab w r) = removeSlot (permTab w) r := by
  decide +kernel

theorem permTab_conjTab : ∀ w : Fin 24, permTab (conjTab w) = piABB * permTab w * piABB⁻¹ := by
  decide +kernel

theorem permTab_swIdx : permTab swIdx = Equiv.swap 0 3 := by decide +kernel

theorem permTab_zero : permTab 0 = 1 := by decide +kernel

/-! ### Unit parts -/

/-- Site table `δ_{s, j}` (24 matrices `1 × 1`). -/
def dTab (j : Fin 24) : List (List (List ℤ)) := (List.range 24).map fun i => [[if i = j.val then 1 else 0]]

/-- Qubit table `s ↦ 2^{cyc(permTab a · permTab s)}`. -/
def qTab (a : Fin 24) : List (List (List ℤ)) :=
  (List.range 24).map fun i => [[(2 : ℤ) ^ cycTab (mulTab a (WernerEndpoint.fin24 i))]]

/-- The `1 × 1` part with site indices `j` and qubit index `a`. -/
def unitPart (fac : ℤ) (j : Fin 3 → Fin 24) (a : Fin 24) : PartData where
  ks := [1, 1, 1, 1]
  k := 1
  X := [[1]]
  Bl := [[1]]
  Br := [[1]]
  fac := fac
  rhos := [dTab (j 0), dTab (j 1), dTab (j 2), qTab a]
  w := 0
  bnd := 0
  folds := []
  Ks := []
  tree := []

theorem ent_dTab (j : Fin 24) {i : ℕ} (hi : i < 24) : ent ((dTab j).getD i []) 0 0 = if i = j.val then 1 else 0 := by
  rw [dTab, getD_map_range _ hi]; rfl

theorem ent_qTab (a : Fin 24) {i : ℕ} (hi : i < 24) :
    ent ((qTab a).getD i []) 0 0 = (2 : ℤ) ^ cycTab (mulTab a (WernerEndpoint.fin24 i)) := by
  rw [qTab, getD_map_range _ hi]; rfl

theorem permIdx_eq_iff (p : P4) (j : Fin 24) : permIdx p = j.val ↔ p = permTab j := by
  constructor
  · intro h; rw [← permTab_permIdx p, h, fin24_val]
  · rintro rfl; exact permIdx_permTab j

theorem cyc_permIdx (a : Fin 24) (q : P4) :
    cycTab (mulTab a (WernerEndpoint.fin24 (permIdx q))) = cycCount (permTab a * q) := by
  rw [← cycCount_permTab, permTab_mulTab, permTab_permIdx]

theorem FTP_unit (fac : ℤ) (j : Fin 3 → Fin 24) (a : Fin 24) (s : Tup (Fin 3)) :
    FTP (unitPart fac j a) s = if s.1 = (fun i => permTab (j i)) then (2 : ℤ) ^ cycCount (permTab a * s.2) else 0 := by
  rw [FTP_eq (unitPart fac j a) 1 1 1 1 rfl s]
  simp only [Fv, K3_nested, Finset.sum_range_one, Ymat, unitPart, rhoE, List.getD_cons_zero,
    List.getD_cons_succ, ent_dTab _ (permIdx_lt _), ent_qTab _ (permIdx_lt _), cyc_permIdx]
  have hY : ent [[(1 : ℤ)]] 0 0 * ent [[1]] 0 0 * ent [[1]] 0 0 = 1 := rfl
  simp only [Nat.add_zero, hY, mul_one]
  have e : ∀ i : Fin 3, (permIdx (s.1 i) = (j i).val) ↔ s.1 i = permTab (j i) := fun i => permIdx_eq_iff _ _
  by_cases h : s.1 = fun i => permTab (j i)
  · simp [h, permIdx_permTab]
  · rw [if_neg h]
    have : ¬ (permIdx (s.1 0) = (j 0).val ∧ permIdx (s.1 1) = (j 1).val ∧ permIdx (s.1 2) = (j 2).val) := by
      rintro ⟨h0, h1, h2⟩
      apply h
      funext i
      fin_cases i
      exacts [(e 0).1 h0, (e 1).1 h1, (e 2).1 h2]
    by_cases h0 : permIdx (s.1 0) = (j 0).val <;> by_cases h1 : permIdx (s.1 1) = (j 1).val <;>
      by_cases h2 : permIdx (s.1 2) = (j 2).val <;> simp_all

/-- The unit part's pairing: `∑_s m(s) FTP s = ∑_q 2^{cyc(a q)} m((permTab j_i)_i, q)`. -/
theorem sum_unit (fac : ℤ) (j : Fin 3 → Fin 24) (a : Fin 24) (m : Tup (Fin 3) → ℝ) :
    ∑ s, m s * (FTP (unitPart fac j a) s : ℝ) =
      ∑ q : P4, (2 : ℝ) ^ cycCount (permTab a * q) * m ((fun i => permTab (j i)), q) := by
  simp only [FTP_unit, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (fun i => permTab (j i))]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [if_true]; push_cast; ring
  · intro w _ hw
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [hw]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **A trace functional is a unit part.** -/
theorem mTr_unit (fac : ℤ) (j : Fin 3 → Fin 24) (a : Fin 24) (w : Fin 3 → P4) (wq : P4)
    (hj : ∀ i, permTab (j i) = (w i)⁻¹) (ha : permTab a = wq) (m : Tup (Fin 3) → ℝ) :
    mTr 2 (w, wq) m = ∑ s, m s * (FTP (unitPart fac j a) s : ℝ) := by
  rw [sum_unit]
  have hj' : (fun i => permTab (j i)) = fun i => (w i)⁻¹ := funext hj
  simp only [mTr, gram, inv_inv, hj', ha]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast; ring

/-! ### Rows and objective as unit parts -/

/-- An integer multiple of a trace functional, in index form. -/
structure UTerm where
  coef : ℤ
  f : Fam
  j : Fin 3 → Fin 24
  a : Fin 24

/-- `∑_s μ_f(s) FTP (unitPart _ j a) s`. -/
noncomputable def UTerm.val (u : UTerm) (μ : Fam → Tup (Fin 3) → ℝ) : ℝ :=
  ∑ s, μ u.f s * (FTP (unitPart 0 u.j u.a) s : ℝ)

/-- The site indices of the inverse words of a row code. -/
def ivj (w0 w1 w2 : Fin 24) : Fin 3 → Fin 24 := ![invTab w0, invTab w1, invTab w2]

/-- A row code as unit terms (the coefficients of `RowCode.row`). -/
def RowCode.uterms : RowCode → List UTerm
  | .trace => [⟨2, .f31, fun _ => 0, 0⟩]
  | .contrast f r w0 w1 w2 wq =>
      [⟨2, f, ivj w0 w1 w2, wq⟩, ⟨-(if permFun wq r = r then 2 else 1), f, ivj w0 w1 w2, remTab wq r⟩]
  | .r3122 w0 w1 w2 wq => [⟨2, .f31, ivj w0 w1 w2, wq⟩, ⟨-2, .f22, ivj w0 w1 w2, wq⟩]
  | .r2213 w0 w1 w2 wq =>
      [⟨2, .f22, ivj w0 w1 w2, wq⟩,
        ⟨-2, .f13, ![conjTab (invTab w0), conjTab (invTab w1), conjTab (invTab w2)], conjTab wq⟩]

theorem ivj_spec (w0 w1 w2 : Fin 24) : ∀ i, permTab (ivj w0 w1 w2 i) = (wOf w0 w1 w2 i)⁻¹ := by
  intro i; fin_cases i <;> simp [ivj, wOf, permTab_invTab]

theorem mRowVal_uterms (c : RowCode) (μ : Fam → Tup (Fin 3) → ℝ) :
    mRowVal 2 c.row μ = (c.uterms.map fun u => (u.coef : ℝ) * u.val μ).sum := by
  cases c with
  | trace =>
    simp only [RowCode.row, RowCode.uterms, mRowVal, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, UTerm.val]
    rw [mTr_unit 0 (fun _ => 0) 0 _ _ (fun i => by simp [permTab_zero]) permTab_zero]
    push_cast; ring
  | contrast f r w0 w1 w2 wq =>
    simp only [RowCode.row, RowCode.uterms, mRowVal, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, UTerm.val]
    rw [mTr_unit 0 _ wq _ _ (ivj_spec w0 w1 w2) rfl,
      mTr_unit 0 _ (remTab wq r) _ _ (ivj_spec w0 w1 w2) (permTab_remTab wq r)]
    by_cases hr : permFun wq r = r <;> simp [permTab_apply, hr] <;> ring
  | r3122 w0 w1 w2 wq =>
    simp only [RowCode.row, RowCode.uterms, mRowVal, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, UTerm.val]
    rw [mTr_unit 0 _ wq _ _ (ivj_spec w0 w1 w2) rfl, mTr_unit 0 _ wq _ _ (ivj_spec w0 w1 w2) rfl]
    push_cast; ring
  | r2213 w0 w1 w2 wq =>
    simp only [RowCode.row, RowCode.uterms, mRowVal, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, UTerm.val]
    have hs : ∀ i, permTab (![conjTab (invTab w0), conjTab (invTab w1), conjTab (invTab w2)] i) =
        (piABB * wOf w0 w1 w2 i * piABB⁻¹)⁻¹ := by
      intro i
      fin_cases i <;> simp [permTab_conjTab, permTab_invTab, wOf, _root_.mul_inv_rev, mul_assoc]
    rw [mTr_unit 0 _ wq _ _ (ivj_spec w0 w1 w2) rfl, mTr_unit 0 _ (conjTab wq) _ _ hs (permTab_conjTab wq)]
    push_cast; ring

/-- The site indices of the objective word for `S`. -/
def objJ (S : Finset (Fin 3)) : Fin 3 → Fin 24 := fun i => if i ∈ S then swIdx else 0

/-- The eight subsets of `Fin 3`. -/
def subsets3 : List (Finset (Fin 3)) := [∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}]

/-- The objective times 8 as unit terms: `8 (−1/2)^{|S|} = (−1)^{|S|} 2^{3−|S|}`. -/
def objUTerms : List UTerm :=
  subsets3.map fun S => ⟨(-1) ^ S.card * 2 ^ (3 - S.card), .f31, objJ S, swIdx⟩

theorem mTr_obj (S : Finset (Fin 3)) (m : Tup (Fin 3) → ℝ) :
    mTr 2 (objSites S, Equiv.swap 0 3) m = ∑ s, m s * (FTP (unitPart 0 (objJ S) swIdx) s : ℝ) := by
  refine mTr_unit 0 _ _ _ _ (fun i => ?_) permTab_swIdx m
  by_cases h : i ∈ S <;> simp [objJ, objSites, h, permTab_swIdx, permTab_zero, Equiv.swap_inv]

theorem subsets3_spec : subsets3.Nodup ∧ subsets3.toFinset = Finset.univ := by decide +kernel

theorem mObj_uterms (μ : Fam → Tup (Fin 3) → ℝ) :
    8 * mObj 2 μ = (objUTerms.map fun u => (u.coef : ℝ) * u.val μ).sum := by
  rw [mObj, ← subsets3_spec.2, List.sum_toFinset _ subsets3_spec.1, ← List.sum_map_mul_left]
  simp only [objUTerms, List.map_map]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun S hS => ?_
  simp only [Function.comp_apply, UTerm.val, mTr_obj]
  have hc : S.card ≤ 3 := by
    have := Finset.card_le_univ S; simpa using this
  have h8 : (8 : ℝ) * (-1 / 2) ^ S.card = (-1) ^ S.card * 2 ^ (3 - S.card) := by
    have e : (8 : ℝ) = 2 ^ (3 - S.card) * 2 ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hc]; norm_num
    rw [e, div_pow]
    field_simp
    try ring
  push_cast
  rw [← mul_assoc, h8]

end LayerDT0

#print axioms LayerDT0.mRowVal_uterms
#print axioms LayerDT0.mObj_uterms
