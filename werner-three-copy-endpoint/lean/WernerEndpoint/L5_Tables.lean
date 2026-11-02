import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import WernerEndpoint.L5_CoupledGram

/-!
# L5, concrete part: the six literal index tables of `verify_d5.py`

`verify_d5.py` (section (B)) defines the coupled-block maps by six lists `mpos` of the eight digit
names `i0 … i3` (row digits) and `j0 … j3` (column digits), read by `literal_map` as
`np.einsum(src + "->abcdefgh", ·)` with `src[k] = "abcdefgh"[NAMES.index(mpos[k])]`.
Input axis `k` (`k < 4`: row digit of copy `k`; `k ≥ 4`: column digit of copy `k - 4`) is filled by
the output digit named `mpos[k]`. In the slot notation of `rearr` (`Sum.inl s` = row digit of
copy `s`, `Sum.inr s` = column digit of copy `s`) this is the bijection

  `σ (inl s) = slot (mpos[s])`, `σ (inr s) = slot (mpos[4 + s])`,

the same convention as `sigma_from_mpos` in `lean/statement_check/check_defs.py`, which checked
numerically that `rearr σ` equals the `literal_map` einsum on all six tables.

* `ofPositions m` is this map for a list `m : Fin 8 → Fin 4 ⊕ Fin 4`; `tableEquiv` packages it with
  its inverse (found by search over the eight slots); the four inverse laws are checked by
  `decide` for each table.
* `Y31 a b`, `Y13 a b`, `Y22 a b` are the rank-one family moments `|aaab⟩⟨aaab|`, `|bbba⟩⟨bbba|`,
  `|aabb⟩⟨aabb|` for arbitrary vectors `a b : ι → R` (one per replica slot).
* `rearr_T3_*`, `rearr_T23_*`: the three rearrangements give `|u⟩⟨u|`, `|v⟩⟨v|`, `|u⟩⟨v|` with
  `u = a a b ā`, `v = b b a b̄` (T = {3}) and `u = b a ā ā`, `v = b b b̄ ā` (T = {2,3}).
* `coupled_block_T3_posSemidef`, `coupled_block_T23_posSemidef`: the coupled blocks
  `[[rearr σ₃₁ Y31, rearr σ₂₂ Y22], [(rearr σ₂₂ Y22)ᴴ, rearr σ₁₃ Y13]]` are PSD.

For T = {3} the verifier's v-map uses the same eight positions as its u-map
(`MAPS["c3"]["13"]` and `MAPS["c3"]["31"]` are built from the same list): `sigmaT3_13 = sigmaT3_31`,
and since `Y13 a b = Y31 b a`, the (2,2) block is the a ↔ b image of the (1,1) block
(`rearr_T3_13_eq_swap`); the literal rule gives `|v⟩⟨v|` with `v = b b a b̄`.

The finite checks use a symbolic encoding: `letter a b c x` is `a` or `b` (by `x`), conjugated when
`c`; `slotFn_letter` reduces the slot factors of a word to the inverse table, which `decide`
evaluates.
-/

open Matrix

namespace WernerEndpoint

-- The verifier's digit names: `iK` = row digit of copy `K`, `jK` = column digit of copy `K`.
namespace Slot

abbrev i0 : Fin 4 ⊕ Fin 4 := .inl 0
abbrev i1 : Fin 4 ⊕ Fin 4 := .inl 1
abbrev i2 : Fin 4 ⊕ Fin 4 := .inl 2
abbrev i3 : Fin 4 ⊕ Fin 4 := .inl 3
abbrev j0 : Fin 4 ⊕ Fin 4 := .inr 0
abbrev j1 : Fin 4 ⊕ Fin 4 := .inr 1
abbrev j2 : Fin 4 ⊕ Fin 4 := .inr 2
abbrev j3 : Fin 4 ⊕ Fin 4 := .inr 3

end Slot

open Slot

section Tables

/-- The slot map of a verifier position list `m = mpos` (eight names `i0 … j3`):
input slot `inl s` (axis `s`) is filled from output slot `m[s]`, input slot `inr s`
(axis `4 + s`) from output slot `m[4 + s]`. -/
def ofPositions (m : Fin 8 → Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl s => m ⟨s.val, by have := s.isLt; omega⟩
  | .inr s => m ⟨s.val + 4, by have := s.isLt; omega⟩

/-- The eight slots in the verifier's order `i0 … i3, j0 … j3`. -/
def allSlots : List (Fin 4 ⊕ Fin 4) := [i0, i1, i2, i3, j0, j1, j2, j3]

/-- Inverse of `ofPositions m` by search over the eight slots (correct when `ofPositions m` is a
bijection, which `tableEquiv` requires). -/
def invPositions (m : Fin 8 → Fin 4 ⊕ Fin 4) (p : Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 :=
  (allSlots.find? fun q => decide (ofPositions m q = p)).getD p

/-- A verifier position list as a bijection of the eight digit slots. -/
def tableEquiv (m : Fin 8 → Fin 4 ⊕ Fin 4)
    (h₁ : ∀ s : Fin 4, invPositions m (ofPositions m (.inl s)) = .inl s)
    (h₂ : ∀ s : Fin 4, invPositions m (ofPositions m (.inr s)) = .inr s)
    (h₃ : ∀ s : Fin 4, ofPositions m (invPositions m (.inl s)) = .inl s)
    (h₄ : ∀ s : Fin 4, ofPositions m (invPositions m (.inr s)) = .inr s) :
    Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 where
  toFun := ofPositions m
  invFun := invPositions m
  left_inv := by
    rintro (s | s)
    exacts [h₁ s, h₂ s]
  right_inv := by
    rintro (s | s)
    exacts [h₃ s, h₄ s]

/-- The bijection `tableEquiv m _ _ _ _` is the verifier's table `ofPositions m`. -/
@[simp] theorem coe_tableEquiv (m : Fin 8 → Fin 4 ⊕ Fin 4) (h₁ h₂ h₃ h₄) :
    ⇑(tableEquiv m h₁ h₂ h₃ h₄) = ofPositions m :=
  rfl

/-- Closes a finite check over `Fin 4` by `decide`, falling back to a case split. -/
macro "table_decide" : tactic =>
  `(tactic| first
    | decide
    | (intro s; fin_cases s <;> first | rfl | exact ⟨rfl, rfl⟩))

/-! The six tables, transcribed from `MAPS` in `exact_certificate_d5/verify_d5.py`
(the T = {2,3} lists are also `NEW["A"]`, `NEW["D"]`, `NEW["X"]` in
`code/relaxations/newcoupled.py`). -/

/-- `MAPS["c3"]["31"]`: `["i0","i1","j3","i2","i3","j0","j1","j2"]`, T = {3}. -/
def sigmaT3_31 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i0, i1, j3, i2, i3, j0, j1, j2]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- `MAPS["c3"]["13"]`: `["i0","i1","j3","i2","i3","j0","j1","j2"]` (the same list as the
u-map), T = {3}. -/
def sigmaT3_13 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i0, i1, j3, i2, i3, j0, j1, j2]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- `MAPS["c3"]["22"]`: `["i0","i1","i2","j3","i3","j2","j0","j1"]`, T = {3}. -/
def sigmaT3_22 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i0, i1, i2, j3, i3, j2, j0, j1]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- `MAPS["c23"]["31"]`: `["i1","j2","j3","i0","i2","i3","j1","j0"]`, T = {2,3}. -/
def sigmaT23_31 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i1, j2, j3, i0, i2, i3, j1, j0]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- `MAPS["c23"]["13"]`: `["i0","i1","j2","j3","i2","j0","j1","i3"]`, T = {2,3}. -/
def sigmaT23_13 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i0, i1, j2, j3, i2, j0, j1, i3]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- `MAPS["c23"]["22"]`: `["i1","j3","i0","j2","i2","i3","j0","j1"]`, T = {2,3}. -/
def sigmaT23_22 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  tableEquiv ![i1, j3, i0, j2, i2, i3, j0, j1]
    (by table_decide) (by table_decide) (by table_decide) (by table_decide)

/-- The verifier's T = {3} v-map is its u-map (the same eight positions). -/
theorem sigmaT3_13_eq_sigmaT3_31 : sigmaT3_13 = sigmaT3_31 :=
  rfl

end Tables

section Words

variable {ι R : Type*} [CommRing R] [StarRing R]

/-- The letter `a` (`x = false`) or `b` (`x = true`), conjugated when `c = true`. -/
def letter (a b : ι → R) (c x : Bool) : ι → R :=
  bif c then star (bif x then b else a) else (bif x then b else a)

theorem star_letter (a b : ι → R) (c x : Bool) : star (letter a b c x) = letter a b (!c) x := by
  cases c
  · rfl
  · first
      | exact star_star (bif x then b else a)
      | simp [letter]

/-- The slot factors of the moment of a word `w` (unconjugated letters) are letters, read off
the inverse table: conjugated iff the slot comes from a column digit. -/
theorem slotFn_letter (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (a b : ι → R) (w : Fin 4 → Bool)
    (p : Fin 4 ⊕ Fin 4) :
    slotFn σ (fun r => letter a b false (w r)) (fun r => letter a b false (w r)) p =
      letter a b (σ.symm p).isRight (w ((σ.symm p).elim id id)) := by
  unfold slotFn
  generalize σ.symm p = q
  cases q <;> rfl

/-- **L5 (word rearrangement, finite form).** If `W = ⊗ (letters of the word w)`, `U`, `V` are
given by letters, and the inverse table of `σ` sends the slots to the right letters (a finite
Bool check), then `rearr σ |W⟩⟨W| = |⊗U⟩⟨⊗V|`. -/
theorem rearr_word (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (a b : ι → R) (W U V : Fin 4 → ι → R)
    (w cu lu cv lv : Fin 4 → Bool)
    (hW : ∀ r, W r = letter a b false (w r)) (hU : ∀ r, U r = letter a b (cu r) (lu r))
    (hV : ∀ r, V r = letter a b (cv r) (lv r))
    (hu : ∀ r, (σ.symm (.inl r)).isRight = cu r ∧ w ((σ.symm (.inl r)).elim id id) = lu r)
    (hv : ∀ r, (!(σ.symm (.inr r)).isRight) = cv r ∧ w ((σ.symm (.inr r)).elim id id) = lv r) :
    rearr σ (vecMulVec (prodVec W) (star (prodVec W))) =
      vecMulVec (prodVec U) (star (prodVec V)) := by
  obtain rfl : W = fun r => letter a b false (w r) := funext hW
  obtain rfl : U = fun r => letter a b (cu r) (lu r) := funext hU
  obtain rfl : V = fun r => letter a b (cv r) (lv r) := funext hV
  have eu : (fun r => slotFn σ (fun r => letter a b false (w r))
      (fun r => letter a b false (w r)) (.inl r)) = fun r => letter a b (cu r) (lu r) := by
    funext r
    rw [slotFn_letter, (hu r).1, (hu r).2]
  have ev : (fun r => star (slotFn σ (fun r => letter a b false (w r))
      (fun r => letter a b false (w r)) (.inr r))) = fun r => letter a b (cv r) (lv r) := by
    funext r
    rw [slotFn_letter, star_letter, (hv r).1, (hv r).2]
  exact (rearr_vecMulVec_prodVec σ (fun r => letter a b false (w r))
    (fun r => letter a b false (w r))).trans
    (congrArg₂ (fun f g : Fin 4 → ι → R => vecMulVec (prodVec f) (star (prodVec g))) eu ev)

/-- Closes `∀ r : Fin 4, X r = letter a b (c r) (x r)` for explicit vectors. -/
macro "letter_cases" : tactic =>
  `(tactic| (intro r; fin_cases r <;> first | rfl | simp [letter]))

/-- The rank-one moment of the family `31`: `|a a a b⟩⟨a a a b|`. -/
def Y31 (a b : ι → R) : Matrix (Fin 4 → ι) (Fin 4 → ι) R :=
  vecMulVec (prodVec (![a, a, a, b] : Fin 4 → ι → R))
    (star (prodVec (![a, a, a, b] : Fin 4 → ι → R)))

/-- The rank-one moment of the family `13`: `|b b b a⟩⟨b b b a|`. -/
def Y13 (a b : ι → R) : Matrix (Fin 4 → ι) (Fin 4 → ι) R :=
  vecMulVec (prodVec (![b, b, b, a] : Fin 4 → ι → R))
    (star (prodVec (![b, b, b, a] : Fin 4 → ι → R)))

/-- The rank-one moment of the family `22`: `|a a b b⟩⟨a a b b|`. -/
def Y22 (a b : ι → R) : Matrix (Fin 4 → ι) (Fin 4 → ι) R :=
  vecMulVec (prodVec (![a, a, b, b] : Fin 4 → ι → R))
    (star (prodVec (![a, a, b, b] : Fin 4 → ι → R)))

/-- T = {3}: `u = a ⊗ a ⊗ b ⊗ ā`. -/
def uT3 (a b : ι → R) : (Fin 4 → ι) → R := prodVec (![a, a, b, star a] : Fin 4 → ι → R)

/-- T = {3}: `v = b ⊗ b ⊗ a ⊗ b̄`. -/
def vT3 (a b : ι → R) : (Fin 4 → ι) → R := prodVec (![b, b, a, star b] : Fin 4 → ι → R)

/-- T = {2,3}: `u = b ⊗ a ⊗ ā ⊗ ā`. -/
def uT23 (a b : ι → R) : (Fin 4 → ι) → R := prodVec (![b, a, star a, star a] : Fin 4 → ι → R)

/-- T = {2,3}: `v = b ⊗ b ⊗ b̄ ⊗ ā`. -/
def vT23 (a b : ι → R) : (Fin 4 → ι) → R := prodVec (![b, b, star b, star a] : Fin 4 → ι → R)

/-! ### T = {3} -/

theorem rearr_T3_31 (a b : ι → R) :
    rearr sigmaT3_31 (Y31 a b) = vecMulVec (uT3 a b) (star (uT3 a b)) := by
  unfold Y31 uT3
  exact rearr_word sigmaT3_31 a b _ _ _ ![false, false, false, true]
    ![false, false, false, true] ![false, false, true, false]
    ![false, false, false, true] ![false, false, true, false]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

theorem rearr_T3_13 (a b : ι → R) :
    rearr sigmaT3_13 (Y13 a b) = vecMulVec (vT3 a b) (star (vT3 a b)) := by
  unfold Y13 vT3
  exact rearr_word sigmaT3_13 a b _ _ _ ![true, true, true, false]
    ![false, false, false, true] ![true, true, false, true]
    ![false, false, false, true] ![true, true, false, true]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

theorem rearr_T3_22 (a b : ι → R) :
    rearr sigmaT3_22 (Y22 a b) = vecMulVec (uT3 a b) (star (vT3 a b)) := by
  unfold Y22 uT3 vT3
  exact rearr_word sigmaT3_22 a b _ _ _ ![false, false, true, true]
    ![false, false, false, true] ![false, false, true, false]
    ![false, false, false, true] ![true, true, false, true]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

/-- The T = {3} (2,2) block is the a ↔ b image of the (1,1) block: the verifier applies the
u-map's positions to `Y13 a b = Y31 b a`, and `vT3 a b = uT3 b a`. -/
theorem rearr_T3_13_eq_swap (a b : ι → R) :
    rearr sigmaT3_13 (Y13 a b) = rearr sigmaT3_31 (Y31 b a) ∧ vT3 a b = uT3 b a :=
  ⟨rfl, rfl⟩

/-- **L5, T = {3}.** The coupled block of `verify_d5.py`'s `MAPS["c3"]` is PSD. -/
theorem coupled_block_T3_posSemidef [Fintype ι] [PartialOrder R] [StarOrderedRing R]
    (a b : ι → R) :
    (fromBlocks (rearr sigmaT3_31 (Y31 a b)) (rearr sigmaT3_22 (Y22 a b))
      (rearr sigmaT3_22 (Y22 a b))ᴴ (rearr sigmaT3_13 (Y13 a b))).PosSemidef :=
  coupled_block_of_rearr₃_posSemidef _ _ _ _ _ _ (uT3 a b) (vT3 a b)
    (rearr_T3_31 a b) (rearr_T3_22 a b) (rearr_T3_13 a b)

/-! ### T = {2,3} -/

theorem rearr_T23_31 (a b : ι → R) :
    rearr sigmaT23_31 (Y31 a b) = vecMulVec (uT23 a b) (star (uT23 a b)) := by
  unfold Y31 uT23
  exact rearr_word sigmaT23_31 a b _ _ _ ![false, false, false, true]
    ![false, false, true, true] ![true, false, false, false]
    ![false, false, true, true] ![true, false, false, false]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

theorem rearr_T23_13 (a b : ι → R) :
    rearr sigmaT23_13 (Y13 a b) = vecMulVec (vT23 a b) (star (vT23 a b)) := by
  unfold Y13 vT23
  exact rearr_word sigmaT23_13 a b _ _ _ ![true, true, true, false]
    ![false, false, true, true] ![true, true, true, false]
    ![false, false, true, true] ![true, true, true, false]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

theorem rearr_T23_22 (a b : ι → R) :
    rearr sigmaT23_22 (Y22 a b) = vecMulVec (uT23 a b) (star (vT23 a b)) := by
  unfold Y22 uT23 vT23
  exact rearr_word sigmaT23_22 a b _ _ _ ![false, false, true, true]
    ![false, false, true, true] ![true, false, false, false]
    ![false, false, true, true] ![true, true, true, false]
    (by letter_cases) (by letter_cases) (by letter_cases) (by table_decide) (by table_decide)

/-- **L5, T = {2,3}.** The coupled block of `verify_d5.py`'s `MAPS["c23"]` is PSD. -/
theorem coupled_block_T23_posSemidef [Fintype ι] [PartialOrder R] [StarOrderedRing R]
    (a b : ι → R) :
    (fromBlocks (rearr sigmaT23_31 (Y31 a b)) (rearr sigmaT23_22 (Y22 a b))
      (rearr sigmaT23_22 (Y22 a b))ᴴ (rearr sigmaT23_13 (Y13 a b))).PosSemidef :=
  coupled_block_of_rearr₃_posSemidef _ _ _ _ _ _ (uT23 a b) (vT23 a b)
    (rearr_T23_31 a b) (rearr_T23_22 a b) (rearr_T23_13 a b)

end Words

end WernerEndpoint

#print axioms WernerEndpoint.coe_tableEquiv
#print axioms WernerEndpoint.sigmaT3_31
#print axioms WernerEndpoint.sigmaT3_13
#print axioms WernerEndpoint.sigmaT3_22
#print axioms WernerEndpoint.sigmaT23_31
#print axioms WernerEndpoint.sigmaT23_13
#print axioms WernerEndpoint.sigmaT23_22
#print axioms WernerEndpoint.sigmaT3_13_eq_sigmaT3_31
#print axioms WernerEndpoint.star_letter
#print axioms WernerEndpoint.slotFn_letter
#print axioms WernerEndpoint.rearr_word
#print axioms WernerEndpoint.rearr_T3_31
#print axioms WernerEndpoint.rearr_T3_13
#print axioms WernerEndpoint.rearr_T3_22
#print axioms WernerEndpoint.rearr_T3_13_eq_swap
#print axioms WernerEndpoint.coupled_block_T3_posSemidef
#print axioms WernerEndpoint.rearr_T23_31
#print axioms WernerEndpoint.rearr_T23_13
#print axioms WernerEndpoint.rearr_T23_22
#print axioms WernerEndpoint.coupled_block_T23_posSemidef
