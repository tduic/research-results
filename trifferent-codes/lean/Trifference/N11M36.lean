import Trifference.Basic

/-! T(11) ≥ 36: explicit trifferent code of length 11 with 36 words.
Word `(p, q)` decodes via `Trifference.dec`: coordinate `i` is 1 if bit `i` of `p` is set,
else 2 if bit `i` of `q` is set, else 0. -/

namespace Trifference

/-- the code, as bitmask pairs -/
def codeN11M36 : List (ℕ × ℕ) := [
  (1208, 256), (32, 1864), (604, 128), (16, 932), (738, 1024), (302, 64), (1810, 4), (2, 1140),
  (570, 1476), (8, 466), (512, 1166), (369, 512), (1573, 8), (1099, 16), (151, 32), (583, 1208),
  (1315, 604), (905, 2), (233, 1810), (1, 570), (285, 738), (1681, 302), (64, 1681), (1476, 1),
  (4, 233), (1140, 905), (1024, 285), (1166, 369), (466, 1573), (128, 1315), (932, 1099), (256, 583),
  (1864, 151), (0, 0), (2047, 0), (0, 2047)]

lemma codeN11M36_check3 : check3 11 codeN11M36 = true := by decide +kernel
lemma codeN11M36_pairs : checkPairs 11 codeN11M36 = true := by decide +kernel
lemma codeN11M36_length : codeN11M36.length = 36 := by decide +kernel

theorem T_ge_N11M36 : ∃ C : Finset (Fin 11 → Fin 3), Trifferent C ∧ 36 ≤ C.card := by
  obtain ⟨h1, h2⟩ := trifferent_of_check 11 codeN11M36 codeN11M36_check3 codeN11M36_pairs
  exact ⟨_, h1, by rw [h2, codeN11M36_length]⟩

end Trifference

#print axioms Trifference.T_ge_N11M36
