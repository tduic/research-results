import Trifference.Basic

/-! T(17) ≥ 109: explicit trifferent code of length 17 with 109 words.
Word `(p, q)` decodes via `Trifference.dec`: coordinate `i` is 1 if bit `i` of `p` is set,
else 2 if bit `i` of `q` is set, else 0. -/

namespace Trifference

/-- the code, as bitmask pairs -/
def codeN17M109 : List (ℕ × ℕ) := [
  (0, 0), (65536, 0), (61590, 69152), (3616, 127126), (55914, 65809), (8396, 120067), (1112, 76709), (273, 121450),
  (11173, 66648), (54531, 73932), (48405, 65536), (16771, 111156), (801, 85122), (26222, 104448), (2264, 90118), (36936, 67248),
  (9220, 82811), (37536, 76109), (18450, 103881), (0, 113941), (19586, 66337), (45620, 82307), (17275, 74756), (38345, 83986),
  (10573, 103072), (38912, 91758), (1712, 102472), (24582, 67800), (1603, 73744), (53445, 67618), (10353, 120452), (56376, 74562),
  (652, 119120), (8202, 69092), (1280, 129065), (2486, 66057), (62208, 66719), (39750, 66561), (26064, 102439), (352, 92817),
  (16429, 106066), (11913, 81988), (36891, 73952), (20, 83240), (46242, 68380), (18944, 110986), (8786, 104708), (18624, 75058),
  (37988, 82816), (24872, 66119), (37784, 93249), (3342, 102641), (47105, 81980), (163, 112136), (17941, 67722), (5879, 90368),
  (32833, 72086), (26689, 100128), (36236, 78434), (17208, 98500), (12554, 85072), (17540, 108569), (6146, 82605), (41520, 70667),
  (35554, 87061), (9280, 98435), (20564, 76321), (153, 102246), (32297, 66000), (32783, 94528), (20864, 66572), (42258, 88744),
  (2852, 106522), (9186, 116736), (6484, 74882), (50496, 70196), (12424, 66163), (49708, 81089), (3098, 114757), (59537, 69896),
  (7, 124856), (5665, 67854), (33350, 85305), (15584, 98575), (16464, 78729), (4373, 99906), (26497, 71796), (35107, 90304),
  (18476, 70656), (42138, 82436), (4616, 108722), (12866, 114732), (240, 80906), (52292, 66200), (10240, 70487), (49792, 75105),
  (5174, 117185), (57657, 67588), (6539, 124432), (1805, 69794), (3923, 94248), (33253, 65562), (28993, 102028), (33792, 76354),
  (23188, 98400), (8226, 87252), (21544, 106769), (142, 88833), (43544, 66983)]

lemma codeN17M109_length : codeN17M109.length = 109 := by decide +kernel
lemma codeN17M109_c0 : suffixChunk (pairsAll 17) codeN17M109 0 6 = true := by decide +kernel
lemma codeN17M109_c6 : suffixChunk (pairsAll 17) codeN17M109 6 6 = true := by decide +kernel
lemma codeN17M109_c12 : suffixChunk (pairsAll 17) codeN17M109 12 6 = true := by decide +kernel
lemma codeN17M109_c18 : suffixChunk (pairsAll 17) codeN17M109 18 6 = true := by decide +kernel
lemma codeN17M109_c24 : suffixChunk (pairsAll 17) codeN17M109 24 6 = true := by decide +kernel
lemma codeN17M109_c30 : suffixChunk (pairsAll 17) codeN17M109 30 6 = true := by decide +kernel
lemma codeN17M109_c36 : suffixChunk (pairsAll 17) codeN17M109 36 6 = true := by decide +kernel
lemma codeN17M109_c42 : suffixChunk (pairsAll 17) codeN17M109 42 6 = true := by decide +kernel
lemma codeN17M109_c48 : suffixChunk (pairsAll 17) codeN17M109 48 6 = true := by decide +kernel
lemma codeN17M109_c54 : suffixChunk (pairsAll 17) codeN17M109 54 6 = true := by decide +kernel
lemma codeN17M109_c60 : suffixChunk (pairsAll 17) codeN17M109 60 6 = true := by decide +kernel
lemma codeN17M109_c66 : suffixChunk (pairsAll 17) codeN17M109 66 6 = true := by decide +kernel
lemma codeN17M109_c72 : suffixChunk (pairsAll 17) codeN17M109 72 6 = true := by decide +kernel
lemma codeN17M109_c78 : suffixChunk (pairsAll 17) codeN17M109 78 6 = true := by decide +kernel
lemma codeN17M109_c84 : suffixChunk (pairsAll 17) codeN17M109 84 6 = true := by decide +kernel
lemma codeN17M109_c90 : suffixChunk (pairsAll 17) codeN17M109 90 6 = true := by decide +kernel
lemma codeN17M109_c96 : suffixChunk (pairsAll 17) codeN17M109 96 6 = true := by decide +kernel
lemma codeN17M109_c102 : suffixChunk (pairsAll 17) codeN17M109 102 6 = true := by decide +kernel
lemma codeN17M109_c108 : suffixChunk (pairsAll 17) codeN17M109 108 1 = true := by decide +kernel
lemma codeN17M109_u6 : suffixChunk (pairsAll 17) codeN17M109 0 (6 + 6) = true :=
  suffixChunk_append _ _ 0 6 6 codeN17M109_c0 codeN17M109_c6
lemma codeN17M109_u12 : suffixChunk (pairsAll 17) codeN17M109 0 (12 + 6) = true :=
  suffixChunk_append _ _ 0 12 6 codeN17M109_u6 codeN17M109_c12
lemma codeN17M109_u18 : suffixChunk (pairsAll 17) codeN17M109 0 (18 + 6) = true :=
  suffixChunk_append _ _ 0 18 6 codeN17M109_u12 codeN17M109_c18
lemma codeN17M109_u24 : suffixChunk (pairsAll 17) codeN17M109 0 (24 + 6) = true :=
  suffixChunk_append _ _ 0 24 6 codeN17M109_u18 codeN17M109_c24
lemma codeN17M109_u30 : suffixChunk (pairsAll 17) codeN17M109 0 (30 + 6) = true :=
  suffixChunk_append _ _ 0 30 6 codeN17M109_u24 codeN17M109_c30
lemma codeN17M109_u36 : suffixChunk (pairsAll 17) codeN17M109 0 (36 + 6) = true :=
  suffixChunk_append _ _ 0 36 6 codeN17M109_u30 codeN17M109_c36
lemma codeN17M109_u42 : suffixChunk (pairsAll 17) codeN17M109 0 (42 + 6) = true :=
  suffixChunk_append _ _ 0 42 6 codeN17M109_u36 codeN17M109_c42
lemma codeN17M109_u48 : suffixChunk (pairsAll 17) codeN17M109 0 (48 + 6) = true :=
  suffixChunk_append _ _ 0 48 6 codeN17M109_u42 codeN17M109_c48
lemma codeN17M109_u54 : suffixChunk (pairsAll 17) codeN17M109 0 (54 + 6) = true :=
  suffixChunk_append _ _ 0 54 6 codeN17M109_u48 codeN17M109_c54
lemma codeN17M109_u60 : suffixChunk (pairsAll 17) codeN17M109 0 (60 + 6) = true :=
  suffixChunk_append _ _ 0 60 6 codeN17M109_u54 codeN17M109_c60
lemma codeN17M109_u66 : suffixChunk (pairsAll 17) codeN17M109 0 (66 + 6) = true :=
  suffixChunk_append _ _ 0 66 6 codeN17M109_u60 codeN17M109_c66
lemma codeN17M109_u72 : suffixChunk (pairsAll 17) codeN17M109 0 (72 + 6) = true :=
  suffixChunk_append _ _ 0 72 6 codeN17M109_u66 codeN17M109_c72
lemma codeN17M109_u78 : suffixChunk (pairsAll 17) codeN17M109 0 (78 + 6) = true :=
  suffixChunk_append _ _ 0 78 6 codeN17M109_u72 codeN17M109_c78
lemma codeN17M109_u84 : suffixChunk (pairsAll 17) codeN17M109 0 (84 + 6) = true :=
  suffixChunk_append _ _ 0 84 6 codeN17M109_u78 codeN17M109_c84
lemma codeN17M109_u90 : suffixChunk (pairsAll 17) codeN17M109 0 (90 + 6) = true :=
  suffixChunk_append _ _ 0 90 6 codeN17M109_u84 codeN17M109_c90
lemma codeN17M109_u96 : suffixChunk (pairsAll 17) codeN17M109 0 (96 + 6) = true :=
  suffixChunk_append _ _ 0 96 6 codeN17M109_u90 codeN17M109_c96
lemma codeN17M109_u102 : suffixChunk (pairsAll 17) codeN17M109 0 (102 + 6) = true :=
  suffixChunk_append _ _ 0 102 6 codeN17M109_u96 codeN17M109_c102
lemma codeN17M109_u108 : suffixChunk (pairsAll 17) codeN17M109 0 (108 + 1) = true :=
  suffixChunk_append _ _ 0 108 1 codeN17M109_u102 codeN17M109_c108
lemma codeN17M109_check3 : check3 17 codeN17M109 = true :=
  check3_of_chunks 17 codeN17M109 (by rw [codeN17M109_length]; exact codeN17M109_u108)
lemma codeN17M109_pairs : checkPairs 17 codeN17M109 = true := by decide +kernel

theorem T_ge_N17M109 : ∃ C : Finset (Fin 17 → Fin 3), Trifferent C ∧ 109 ≤ C.card := by
  obtain ⟨h1, h2⟩ := trifferent_of_check 17 codeN17M109 codeN17M109_check3 codeN17M109_pairs
  exact ⟨_, h1, by rw [h2, codeN17M109_length]⟩

end Trifference

#print axioms Trifference.T_ge_N17M109
