import Trifference.Basic

/-! T(10) ≥ 30: explicit trifferent code of length 10 with 30 words.
Word `(p, q)` decodes via `Trifference.dec`: coordinate `i` is 1 if bit `i` of `p` is set,
else 2 if bit `i` of `q` is set, else 0. -/

namespace Trifference

/-- the code, as bitmask pairs -/
def codeN10M30 : List (ℕ × ℕ) := [
  (88, 384), (22, 96), (158, 352), (6, 632), (24, 482), (517, 24), (551, 88), (385, 6),
  (905, 22), (513, 158), (352, 513), (632, 385), (96, 905), (482, 517), (384, 551), (132, 296),
  (334, 528), (66, 644), (74, 916), (264, 530), (229, 264), (595, 132), (313, 66), (33, 74),
  (161, 334), (528, 161), (916, 33), (644, 313), (530, 229), (296, 595)]

lemma codeN10M30_length : codeN10M30.length = 30 := by decide +kernel
lemma codeN10M30_c0 : suffixChunk (pairsAll 10) codeN10M30 0 8 = true := by decide +kernel
lemma codeN10M30_c8 : suffixChunk (pairsAll 10) codeN10M30 8 8 = true := by decide +kernel
lemma codeN10M30_c16 : suffixChunk (pairsAll 10) codeN10M30 16 8 = true := by decide +kernel
lemma codeN10M30_c24 : suffixChunk (pairsAll 10) codeN10M30 24 6 = true := by decide +kernel
lemma codeN10M30_u8 : suffixChunk (pairsAll 10) codeN10M30 0 (8 + 8) = true :=
  suffixChunk_append _ _ 0 8 8 codeN10M30_c0 codeN10M30_c8
lemma codeN10M30_u16 : suffixChunk (pairsAll 10) codeN10M30 0 (16 + 8) = true :=
  suffixChunk_append _ _ 0 16 8 codeN10M30_u8 codeN10M30_c16
lemma codeN10M30_u24 : suffixChunk (pairsAll 10) codeN10M30 0 (24 + 6) = true :=
  suffixChunk_append _ _ 0 24 6 codeN10M30_u16 codeN10M30_c24
lemma codeN10M30_check3 : check3 10 codeN10M30 = true :=
  check3_of_chunks 10 codeN10M30 (by rw [codeN10M30_length]; exact codeN10M30_u24)
lemma codeN10M30_pairs : checkPairs 10 codeN10M30 = true := by decide +kernel

theorem T_ge_N10M30 : ∃ C : Finset (Fin 10 → Fin 3), Trifferent C ∧ 30 ≤ C.card := by
  obtain ⟨h1, h2⟩ := trifferent_of_check 10 codeN10M30 codeN10M30_check3 codeN10M30_pairs
  exact ⟨_, h1, by rw [h2, codeN10M30_length]⟩

end Trifference

#print axioms Trifference.T_ge_N10M30
