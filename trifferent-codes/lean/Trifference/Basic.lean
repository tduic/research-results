import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic

/-!
# Trifferent codes: definition and a verified bitmask checker

`Trifferent C` : every three distinct codewords of `C ⊆ {0,1,2}^n` have a coordinate
where all three differ.  A codeword is given to the checker as a pair of bitmasks
`(p, q)`: bit `i` of `p` marks symbol 1 at coordinate `i`, bit `i` of `q` (and not `p`)
marks symbol 2, otherwise the symbol is 0.  `check3 n L = true` and `checkPairs n L = true`
are evaluated by the kernel (`decide +kernel`); `trifferent_of_check` turns them into the
Mathlib-level statement.
-/

namespace Trifference

/-- Trifferent code (as in the problem statement). -/
def Trifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i

/-- Decode a bitmask pair into a word of `{0,1,2}^n`. -/
def dec (n : ℕ) (w : ℕ × ℕ) : Fin n → Fin 3 := fun i =>
  if w.1.testBit i then 1 else if w.2.testBit i then 2 else 0

/-- indicator masks of symbols 0, 1, 2 on the first `n` coordinates -/
def e1 (n : ℕ) (w : ℕ × ℕ) : ℕ := w.1 &&& (2 ^ n - 1)
def e2 (n : ℕ) (w : ℕ × ℕ) : ℕ := ((w.1 ||| w.2) ^^^ w.1) &&& (2 ^ n - 1)
def e0 (n : ℕ) (w : ℕ × ℕ) : ℕ := (2 ^ n - 1) ^^^ ((w.1 ||| w.2) &&& (2 ^ n - 1))

/-- mask of coordinates where `a, b, c` are pairwise distinct -/
def rainbow (n : ℕ) (a b c : ℕ × ℕ) : ℕ :=
  (e0 n a &&& e1 n b &&& e2 n c) ||| (e0 n a &&& e2 n b &&& e1 n c) |||
  (e1 n a &&& e0 n b &&& e2 n c) ||| (e1 n a &&& e2 n b &&& e0 n c) |||
  (e2 n a &&& e0 n b &&& e1 n c) ||| (e2 n a &&& e1 n b &&& e0 n c)

/-- mask of coordinates where `a, b` differ -/
def diff (n : ℕ) (a b : ℕ × ℕ) : ℕ := (e1 n a ^^^ e1 n b) ||| (e2 n a ^^^ e2 n b)

/-- all pairs `(b, c)`, `b` before `c` in `l`, form a rainbow triple with `a` -/
def pairsAll (n : ℕ) (a : ℕ × ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | b :: l => l.all (fun c => rainbow n a b c != 0) && pairsAll n a l

/-- every 3-element sublist is rainbow somewhere -/
def check3 (n : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | a :: l => pairsAll n a l && check3 n l

/-- every 2-element sublist consists of different words -/
def checkPairs (n : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | a :: l => l.all (fun b => diff n a b != 0) && checkPairs n l

/-- semantic triple property -/
def Sep {n : ℕ} (x y z : Fin n → Fin 3) : Prop :=
  ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i

lemma Sep.swap12 {n : ℕ} {x y z : Fin n → Fin 3} (h : Sep x y z) : Sep y x z := by
  obtain ⟨i, h1, h2, h3⟩ := h; exact ⟨i, Ne.symm h1, h3, h2⟩

lemma Sep.swap23 {n : ℕ} {x y z : Fin n → Fin 3} (h : Sep x y z) : Sep x z y := by
  obtain ⟨i, h1, h2, h3⟩ := h; exact ⟨i, h3, Ne.symm h2, h1⟩

lemma testBit_full (n i : ℕ) : (2 ^ n - 1).testBit i = decide (i < n) :=
  Nat.testBit_two_pow_sub_one n i

lemma rainbow_sound (n : ℕ) (a b c : ℕ × ℕ) (h : rainbow n a b c ≠ 0) :
    Sep (dec n a) (dec n b) (dec n c) := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  simp only [rainbow, e0, e1, e2, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    testBit_full] at hi
  by_cases hin : i < n
  · refine ⟨⟨i, hin⟩, ?_⟩
    simp only [dec]
    simp only [hin, decide_true] at hi
    cases ha1 : a.1.testBit i <;> cases ha2 : a.2.testBit i <;>
    cases hb1 : b.1.testBit i <;> cases hb2 : b.2.testBit i <;>
    cases hc1 : c.1.testBit i <;> cases hc2 : c.2.testBit i <;>
    simp_all
  · simp [hin] at hi

lemma diff_sound (n : ℕ) (a b : ℕ × ℕ) (h : diff n a b ≠ 0) : dec n a ≠ dec n b := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  simp only [diff, e1, e2, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    testBit_full] at hi
  by_cases hin : i < n
  · intro heq
    have := congrFun heq ⟨i, hin⟩
    simp only [dec] at this
    simp only [hin, decide_true] at hi
    cases ha1 : a.1.testBit i <;> cases ha2 : a.2.testBit i <;>
    cases hb1 : b.1.testBit i <;> cases hb2 : b.2.testBit i <;>
    simp_all
  · simp [hin] at hi

lemma pairsAll_sound (n : ℕ) (a : ℕ × ℕ) :
    ∀ l : List (ℕ × ℕ), pairsAll n a l = true →
      ∀ b ∈ l, ∀ c ∈ l, dec n b ≠ dec n c → Sep (dec n a) (dec n b) (dec n c)
  | [], _ => by simp
  | y :: t, h => by
    simp only [pairsAll, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    intro b hb c hc hbc
    rcases List.mem_cons.1 hb with hby | hbt
    · rcases List.mem_cons.1 hc with hcy | hct
      · exact absurd (hby.trans hcy.symm ▸ rfl) hbc
      · subst hby; exact rainbow_sound n a b c (h1 c hct)
    · rcases List.mem_cons.1 hc with hcy | hct
      · subst hcy; exact (rainbow_sound n a c b (h1 b hbt)).swap23
      · exact pairsAll_sound n a t h2 b hbt c hct hbc

lemma check3_sound (n : ℕ) :
    ∀ L : List (ℕ × ℕ), check3 n L = true →
      ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, dec n a ≠ dec n b → dec n b ≠ dec n c →
        dec n a ≠ dec n c → Sep (dec n a) (dec n b) (dec n c)
  | [], _ => by simp
  | x :: l, h => by
    simp only [check3, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro a ha b hb c hc hab hbc hac
    have mem : ∀ u ∈ x :: l, dec n u ≠ dec n x → u ∈ l := fun u hu hne => by
      rcases List.mem_cons.1 hu with rfl | hu
      · exact absurd rfl hne
      · exact hu
    by_cases hax : a = x
    · subst hax
      exact pairsAll_sound n a l h1 b (mem b hb (Ne.symm hab)) c (mem c hc (Ne.symm hac)) hbc
    by_cases hbx : b = x
    · subst hbx
      exact (pairsAll_sound n b l h1 a (mem a ha hab) c (mem c hc (Ne.symm hbc)) hac).swap12
    by_cases hcx : c = x
    · subst hcx
      exact ((pairsAll_sound n c l h1 a (mem a ha hac) b (mem b hb hbc) hab).swap12).swap23
    have ha' : a ∈ l := by rcases List.mem_cons.1 ha with h | h; exact absurd h hax; exact h
    have hb' : b ∈ l := by rcases List.mem_cons.1 hb with h | h; exact absurd h hbx; exact h
    have hc' : c ∈ l := by rcases List.mem_cons.1 hc with h | h; exact absurd h hcx; exact h
    exact check3_sound n l h2 a ha' b hb' c hc' hab hbc hac

lemma checkPairs_sound (n : ℕ) :
    ∀ L : List (ℕ × ℕ), checkPairs n L = true → (L.map (dec n)).Nodup
  | [], _ => by simp
  | x :: l, h => by
    simp only [checkPairs, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun b hb heq => diff_sound n x b (h1 b hb) heq.symm, checkPairs_sound n l h2⟩

/-- Soundness of the checker: a list passing both checks gives a trifferent code
of size `L.length`. -/
theorem trifferent_of_check (n : ℕ) (L : List (ℕ × ℕ))
    (h3 : check3 n L = true) (h2 : checkPairs n L = true) :
    Trifferent (L.map (dec n)).toFinset ∧ (L.map (dec n)).toFinset.card = L.length := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    simp only [List.mem_toFinset, List.mem_map] at hx hy hz
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨c, hc, rfl⟩ := hz
    exact check3_sound n L h3 a ha b hb c hc hxy hyz hxz
  · rw [List.toFinset_card_of_nodup (checkPairs_sound n L h2), List.length_map]

end Trifference

namespace Trifference

/-! ### Chunked checking (keeps each kernel evaluation small) -/

/-- `f` applied to the `k`-th element and the suffix after it, for `k ∈ [s, s+c)`. -/
def suffixChunk (f : ℕ × ℕ → List (ℕ × ℕ) → Bool) (L : List (ℕ × ℕ)) (s c : ℕ) : Bool :=
  (List.range' s c).all (fun k => f (L.getD k (0, 0)) (L.drop (k + 1)))

lemma suffixChunk_append (f : ℕ × ℕ → List (ℕ × ℕ) → Bool) (L : List (ℕ × ℕ)) (s a b : ℕ)
    (h1 : suffixChunk f L s a = true) (h2 : suffixChunk f L (s + a) b = true) :
    suffixChunk f L s (a + b) = true := by
  simp only [suffixChunk, List.all_eq_true] at *
  intro k hk
  rw [← List.range'_append_1] at hk
  rcases List.mem_append.1 hk with hk | hk
  · exact h1 k hk
  · exact h2 k hk

lemma rec_of_suffix (f : ℕ × ℕ → List (ℕ × ℕ) → Bool) (g : List (ℕ × ℕ) → Bool)
    (hnil : g [] = true) (hcons : ∀ a l, g (a :: l) = (f a l && g l)) :
    ∀ L : List (ℕ × ℕ), suffixChunk f L 0 L.length = true → g L = true
  | [], _ => hnil
  | a :: l, h => by
    simp only [suffixChunk, List.all_eq_true, List.mem_range'_1] at h
    rw [hcons, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), rec_of_suffix f g hnil hcons l ?_⟩
    simp only [suffixChunk, List.all_eq_true, List.mem_range'_1]
    intro k hk
    have := h (k + 1) (by simp at hk ⊢; omega)
    simpa using this

lemma check3_of_chunks (n : ℕ) (L : List (ℕ × ℕ))
    (h : suffixChunk (pairsAll n) L 0 L.length = true) : check3 n L = true :=
  rec_of_suffix (pairsAll n) (check3 n) rfl (fun _ _ => rfl) L h

lemma checkPairs_of_chunks (n : ℕ) (L : List (ℕ × ℕ))
    (h : suffixChunk (fun a l => l.all (fun b => diff n a b != 0)) L 0 L.length = true) :
    checkPairs n L = true :=
  rec_of_suffix _ (checkPairs n) rfl (fun _ _ => rfl) L h

end Trifference
