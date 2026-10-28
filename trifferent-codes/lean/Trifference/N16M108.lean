import Trifference.Basic

/-! T(16) ≥ 108: explicit trifferent code of length 16 with 108 words.
Word `(p, q)` decodes via `Trifference.dec`: coordinate `i` is 1 if bit `i` of `p` is set,
else 2 if bit `i` of `q` is set, else 0. -/

namespace Trifference

/-- the code, as bitmask pairs -/
def codeN16M108 : List (ℕ × ℕ) := [
  (0, 0), (61590, 3616), (3616, 61590), (55914, 273), (8396, 54531), (1112, 11173), (273, 55914), (11173, 1112),
  (54531, 8396), (48405, 0), (16771, 45620), (801, 19586), (26222, 38912), (2264, 24582), (36936, 1712), (9220, 17275),
  (37536, 10573), (18450, 38345), (0, 48405), (19586, 801), (45620, 16771), (17275, 9220), (38345, 18450), (10573, 37536),
  (38912, 26222), (1712, 36936), (24582, 2264), (1603, 8208), (53445, 2082), (10353, 54916), (56376, 9026), (652, 53584),
  (8202, 3556), (1280, 63529), (2486, 521), (62208, 1183), (39750, 1025), (26064, 36903), (352, 27281), (16429, 40530),
  (11913, 16452), (36891, 8416), (20, 17704), (46242, 2844), (18944, 45450), (8786, 39172), (18624, 9522), (37988, 17280),
  (24872, 583), (37784, 27713), (3342, 37105), (47105, 16444), (163, 46600), (17941, 2186), (5879, 24832), (32833, 6550),
  (26689, 34592), (36236, 12898), (17208, 32964), (12554, 19536), (17540, 43033), (6146, 17069), (41520, 5131), (35554, 21525),
  (9280, 32899), (20564, 10785), (153, 36710), (32297, 464), (32783, 28992), (20864, 1036), (42258, 23208), (2852, 40986),
  (9186, 51200), (6484, 9346), (50496, 4660), (12424, 627), (49708, 15553), (3098, 49221), (59537, 4360), (7, 59320),
  (5665, 2318), (33350, 19769), (15584, 33039), (16464, 13193), (4373, 34370), (26497, 6260), (35107, 24768), (18476, 5120),
  (42138, 16900), (4616, 43186), (12866, 49196), (240, 15370), (52292, 664), (10240, 4951), (49792, 9569), (5174, 51649),
  (57657, 2052), (6539, 58896), (1805, 4258), (3923, 28712), (33253, 26), (28993, 36492), (33792, 10818), (23188, 32864),
  (8226, 21716), (21544, 41233), (142, 23297), (43544, 1447)]

lemma codeN16M108_length : codeN16M108.length = 108 := by decide +kernel
lemma codeN16M108_c0 : suffixChunk (pairsAll 16) codeN16M108 0 6 = true := by decide +kernel
lemma codeN16M108_c6 : suffixChunk (pairsAll 16) codeN16M108 6 6 = true := by decide +kernel
lemma codeN16M108_c12 : suffixChunk (pairsAll 16) codeN16M108 12 6 = true := by decide +kernel
lemma codeN16M108_c18 : suffixChunk (pairsAll 16) codeN16M108 18 6 = true := by decide +kernel
lemma codeN16M108_c24 : suffixChunk (pairsAll 16) codeN16M108 24 6 = true := by decide +kernel
lemma codeN16M108_c30 : suffixChunk (pairsAll 16) codeN16M108 30 6 = true := by decide +kernel
lemma codeN16M108_c36 : suffixChunk (pairsAll 16) codeN16M108 36 6 = true := by decide +kernel
lemma codeN16M108_c42 : suffixChunk (pairsAll 16) codeN16M108 42 6 = true := by decide +kernel
lemma codeN16M108_c48 : suffixChunk (pairsAll 16) codeN16M108 48 6 = true := by decide +kernel
lemma codeN16M108_c54 : suffixChunk (pairsAll 16) codeN16M108 54 6 = true := by decide +kernel
lemma codeN16M108_c60 : suffixChunk (pairsAll 16) codeN16M108 60 6 = true := by decide +kernel
lemma codeN16M108_c66 : suffixChunk (pairsAll 16) codeN16M108 66 6 = true := by decide +kernel
lemma codeN16M108_c72 : suffixChunk (pairsAll 16) codeN16M108 72 6 = true := by decide +kernel
lemma codeN16M108_c78 : suffixChunk (pairsAll 16) codeN16M108 78 6 = true := by decide +kernel
lemma codeN16M108_c84 : suffixChunk (pairsAll 16) codeN16M108 84 6 = true := by decide +kernel
lemma codeN16M108_c90 : suffixChunk (pairsAll 16) codeN16M108 90 6 = true := by decide +kernel
lemma codeN16M108_c96 : suffixChunk (pairsAll 16) codeN16M108 96 6 = true := by decide +kernel
lemma codeN16M108_c102 : suffixChunk (pairsAll 16) codeN16M108 102 6 = true := by decide +kernel
lemma codeN16M108_u6 : suffixChunk (pairsAll 16) codeN16M108 0 (6 + 6) = true :=
  suffixChunk_append _ _ 0 6 6 codeN16M108_c0 codeN16M108_c6
lemma codeN16M108_u12 : suffixChunk (pairsAll 16) codeN16M108 0 (12 + 6) = true :=
  suffixChunk_append _ _ 0 12 6 codeN16M108_u6 codeN16M108_c12
lemma codeN16M108_u18 : suffixChunk (pairsAll 16) codeN16M108 0 (18 + 6) = true :=
  suffixChunk_append _ _ 0 18 6 codeN16M108_u12 codeN16M108_c18
lemma codeN16M108_u24 : suffixChunk (pairsAll 16) codeN16M108 0 (24 + 6) = true :=
  suffixChunk_append _ _ 0 24 6 codeN16M108_u18 codeN16M108_c24
lemma codeN16M108_u30 : suffixChunk (pairsAll 16) codeN16M108 0 (30 + 6) = true :=
  suffixChunk_append _ _ 0 30 6 codeN16M108_u24 codeN16M108_c30
lemma codeN16M108_u36 : suffixChunk (pairsAll 16) codeN16M108 0 (36 + 6) = true :=
  suffixChunk_append _ _ 0 36 6 codeN16M108_u30 codeN16M108_c36
lemma codeN16M108_u42 : suffixChunk (pairsAll 16) codeN16M108 0 (42 + 6) = true :=
  suffixChunk_append _ _ 0 42 6 codeN16M108_u36 codeN16M108_c42
lemma codeN16M108_u48 : suffixChunk (pairsAll 16) codeN16M108 0 (48 + 6) = true :=
  suffixChunk_append _ _ 0 48 6 codeN16M108_u42 codeN16M108_c48
lemma codeN16M108_u54 : suffixChunk (pairsAll 16) codeN16M108 0 (54 + 6) = true :=
  suffixChunk_append _ _ 0 54 6 codeN16M108_u48 codeN16M108_c54
lemma codeN16M108_u60 : suffixChunk (pairsAll 16) codeN16M108 0 (60 + 6) = true :=
  suffixChunk_append _ _ 0 60 6 codeN16M108_u54 codeN16M108_c60
lemma codeN16M108_u66 : suffixChunk (pairsAll 16) codeN16M108 0 (66 + 6) = true :=
  suffixChunk_append _ _ 0 66 6 codeN16M108_u60 codeN16M108_c66
lemma codeN16M108_u72 : suffixChunk (pairsAll 16) codeN16M108 0 (72 + 6) = true :=
  suffixChunk_append _ _ 0 72 6 codeN16M108_u66 codeN16M108_c72
lemma codeN16M108_u78 : suffixChunk (pairsAll 16) codeN16M108 0 (78 + 6) = true :=
  suffixChunk_append _ _ 0 78 6 codeN16M108_u72 codeN16M108_c78
lemma codeN16M108_u84 : suffixChunk (pairsAll 16) codeN16M108 0 (84 + 6) = true :=
  suffixChunk_append _ _ 0 84 6 codeN16M108_u78 codeN16M108_c84
lemma codeN16M108_u90 : suffixChunk (pairsAll 16) codeN16M108 0 (90 + 6) = true :=
  suffixChunk_append _ _ 0 90 6 codeN16M108_u84 codeN16M108_c90
lemma codeN16M108_u96 : suffixChunk (pairsAll 16) codeN16M108 0 (96 + 6) = true :=
  suffixChunk_append _ _ 0 96 6 codeN16M108_u90 codeN16M108_c96
lemma codeN16M108_u102 : suffixChunk (pairsAll 16) codeN16M108 0 (102 + 6) = true :=
  suffixChunk_append _ _ 0 102 6 codeN16M108_u96 codeN16M108_c102
lemma codeN16M108_check3 : check3 16 codeN16M108 = true :=
  check3_of_chunks 16 codeN16M108 (by rw [codeN16M108_length]; exact codeN16M108_u102)
lemma codeN16M108_pairs : checkPairs 16 codeN16M108 = true := by decide +kernel

theorem T_ge_N16M108 : ∃ C : Finset (Fin 16 → Fin 3), Trifferent C ∧ 108 ≤ C.card := by
  obtain ⟨h1, h2⟩ := trifferent_of_check 16 codeN16M108 codeN16M108_check3 codeN16M108_pairs
  exact ⟨_, h1, by rw [h2, codeN16M108_length]⟩

end Trifference

#print axioms Trifference.T_ge_N16M108
