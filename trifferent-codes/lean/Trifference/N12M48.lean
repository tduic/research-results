import Trifference.Basic

/-! T(12) ≥ 48: explicit trifferent code of length 12 with 48 words.
Word `(p, q)` decodes via `Trifference.dec`: coordinate `i` is 1 if bit `i` of `p` is set,
else 2 if bit `i` of `q` is set, else 0. -/

namespace Trifference

/-- the code, as bitmask pairs -/
def codeN12M48 : List (ℕ × ℕ) := [
  (3640, 448), (448, 3640), (28, 1792), (1792, 28), (910, 112), (112, 910), (3073, 112), (2275, 1792),
  (7, 448), (7, 3640), (2275, 28), (3073, 910), (112, 3073), (910, 3073), (1792, 2275), (28, 2275),
  (448, 7), (3640, 7), (2216, 1808), (1136, 2696), (554, 452), (2594, 1052), (284, 674), (1796, 2186),
  (113, 1796), (3137, 284), (263, 1136), (71, 2216), (449, 2594), (3089, 554), (452, 3089), (1052, 449),
  (674, 3137), (2186, 113), (1808, 71), (2696, 263), (1800, 2160), (450, 540), (135, 1800), (3105, 450),
  (540, 3105), (2160, 135), (546, 2184), (2184, 546), (1365, 2184), (1365, 546), (2184, 1365), (546, 1365)]

lemma codeN12M48_check3 : check3 12 codeN12M48 = true := by decide +kernel
lemma codeN12M48_pairs : checkPairs 12 codeN12M48 = true := by decide +kernel
lemma codeN12M48_length : codeN12M48.length = 48 := by decide +kernel

theorem T_ge_N12M48 : ∃ C : Finset (Fin 12 → Fin 3), Trifferent C ∧ 48 ≤ C.card := by
  obtain ⟨h1, h2⟩ := trifferent_of_check 12 codeN12M48 codeN12M48_check3 codeN12M48_pairs
  exact ⟨_, h1, by rw [h2, codeN12M48_length]⟩

end Trifference

#print axioms Trifference.T_ge_N12M48
