import LayerDProto.PDSound
import LayerDProto.R2Kernel
import Mathlib.Data.List.GetD

/-!
# Layer D, (E′): soundness of the checked per-part kernel computation

Stage A: specifications of the list primitives (`nth`, `chunks`, `sumRows`, `level`) as finite sums.
-/

open Finset

namespace LayerDProto

/-- Entry `(i, j)` of a list of rows (missing entries are `0`). -/
def ent (L : List (List ℤ)) (i j : ℕ) : ℤ := (L.getD i []).getD j 0

theorem nth_eq_getD {α : Type} (l : List α) (i : ℕ) (d : α) : nth l i d = l.getD i d := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => simp [nth, ih]

/-! ### `chunks` -/

theorem chunks_spec {α : Type} (k : ℕ) (hk : 0 < k) :
    ∀ (m f : ℕ) (l : List α), l.length = k * m → m ≤ f →
      (chunks k f l).length = m ∧ ∀ a < m, (chunks k f l).getD a [] = (l.drop (a * k)).take k
  | 0, f, l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    cases f <;> exact ⟨rfl, fun a ha => absurd ha (by omega)⟩
  | m + 1, f, l, hl, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    cases l with
    | nil => simp at hl; nlinarith
    | cons x xs =>
      have hd : ((x :: xs).drop k).length = k * m := by
        rw [List.length_drop, hl]; rw [Nat.mul_succ]; omega
      obtain ⟨ih1, ih2⟩ := chunks_spec k hk m f ((x :: xs).drop k) hd (by omega)
      refine ⟨by simp [chunks, ih1], fun a ha => ?_⟩
      cases a with
      | zero => simp [chunks]
      | succ a =>
        simp only [chunks, List.getD_cons_succ]
        rw [ih2 a (by omega), List.drop_drop]
        congr 2
        ring

theorem getD_take_drop {α : Type} (l : List α) (s k b : ℕ) (hb : b < k) (d : α) :
    ((l.drop s).take k).getD b d = l.getD (s + b) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hb]

/-! ### `sumRows` and `dot` on chunks -/

theorem sumRows_spec (c : ℕ) :
    ∀ (rs : List (List ℤ)), rs ≠ [] → (∀ r ∈ rs, r.length = c) →
      (sumRows rs).length = c ∧ ∀ j < c, (sumRows rs).getD j 0 = ∑ i ∈ range rs.length, ent rs i j
  | [], h, _ => absurd rfl h
  | [r], _, hl => by
    have hr := hl r (by simp)
    exact ⟨hr, fun j _ => by simp [sumRows, ent]⟩
  | r :: s :: rs, _, hl => by
    have hr := hl r (by simp)
    obtain ⟨ih1, ih2⟩ := sumRows_spec c (s :: rs) (by simp) fun r' hr' => hl r' (by simp [hr'])
    have e : sumRows (r :: s :: rs) = List.zipWith (· + ·) r (sumRows (s :: rs)) := rfl
    refine ⟨by rw [e, List.length_zipWith, hr, ih1, min_self], fun j hj => ?_⟩
    have hsh : ∀ i, ent (r :: s :: rs) (i + 1) j = ent (s :: rs) i j := fun i => by simp [ent]
    rw [e, List.length_cons, sum_range_succ']
    simp only [hsh]
    rw [← ih2 j hj]
    have hj1 : j < r.length := hr ▸ hj
    have hj2 : j < (sumRows (s :: rs)).length := ih1 ▸ hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, hj1, hj2, ent, add_comm]


theorem dot_chunk (k : ℕ) (rc row : List ℤ) (hrc : rc.length = k) (b : ℕ) :
    dot rc ((row.drop (b * k)).take k) = ∑ e ∈ range k, rc.getD e 0 * row.getD (b * k + e) 0 := by
  rw [dot_eq, hrc]
  refine sum_congr rfl fun e he => ?_
  rw [getD_take_drop row (b * k) k e (mem_range.mp he)]

/-- One output row of `level`, entry `b`. -/
theorem level_row_spec (k m' : ℕ) (hk : 0 < k) (r grp : List (List ℤ)) (hr : r.length = k)
    (hrc : ∀ rc ∈ r, rc.length = k) (hg : grp.length = k) (hrow : ∀ row ∈ grp, row.length = k * m') :
    (sumRows (List.zipWith (fun row rc => (chunks k row.length row).map fun bg => dot rc bg) grp r)).length = m' ∧
      ∀ b < m', (sumRows (List.zipWith (fun row rc => (chunks k row.length row).map fun bg => dot rc bg)
        grp r)).getD b 0 = ∑ c ∈ range k, ∑ e ∈ range k, ent r c e * ent grp c (b * k + e) := by
  set Z := List.zipWith (fun row rc => (chunks k row.length row).map fun bg => dot rc bg) grp r with hZ
  have hZl : Z.length = k := by rw [hZ, List.length_zipWith, hg, hr, min_self]
  -- the rows of `Z`
  have hZc : ∀ c < k, Z.getD c [] =
      ((chunks k (grp.getD c []).length (grp.getD c [])).map fun bg => dot (r.getD c []) bg) := by
    intro c hc
    have h1 : c < grp.length := hg ▸ hc
    have h2 : c < r.length := hr ▸ hc
    simp [hZ, List.getD_eq_getElem?_getD, List.getElem?_zipWith, h1, h2]
  have hrowc : ∀ c < k, (grp.getD c []).length = k * m' := by
    intro c hc
    have h1 : c < grp.length := hg ▸ hc
    exact hrow _ (by simp [List.getD_eq_getElem?_getD, h1, List.getElem_mem])
  have hrcc : ∀ c < k, (r.getD c []).length = k := by
    intro c hc
    have h2 : c < r.length := hr ▸ hc
    exact hrc _ (by simp [List.getD_eq_getElem?_getD, h2, List.getElem_mem])
  have hZrow : ∀ c < k, (Z.getD c []).length = m' ∧ ∀ b < m', (Z.getD c []).getD b 0 =
      ∑ e ∈ range k, ent r c e * ent grp c (b * k + e) := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := chunks_spec k hk m' (grp.getD c []).length (grp.getD c []) (hrowc c hc)
      (by rw [hrowc c hc]; nlinarith)
    rw [hZc c hc]
    refine ⟨by rw [List.length_map, hc1], fun b hb => ?_⟩
    have hb' : b < (chunks k (grp.getD c []).length (grp.getD c [])).length := hc1 ▸ hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb', Option.map_some,
      Option.getD_some, ← List.getD_eq_getElem _ [] hb', hc2 b hb, dot_chunk k _ _ (hrcc c hc)]
    rfl
  have hne : Z ≠ [] := by
    intro h; rw [h] at hZl; simp at hZl; omega
  have hlen : ∀ z ∈ Z, z.length = m' := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hz
    have := (hZrow c (hZl ▸ hc)).1
    rwa [List.getD_eq_getElem _ [] hc] at this
  obtain ⟨hs1, hs2⟩ := sumRows_spec m' Z hne hlen
  refine ⟨hs1, fun b hb => ?_⟩
  rw [hs2 b hb, hZl]
  exact sum_congr rfl fun c hc => (hZrow c (mem_range.mp hc)).2 b hb

/-- **`level`**: contracts the fastest index of rows and columns against the `k × k` table `r`. -/
theorem level_spec (k m m' : ℕ) (hk : 0 < k) (r rows : List (List ℤ)) (hr : r.length = k)
    (hrc : ∀ rc ∈ r, rc.length = k) (hl : rows.length = k * m)
    (hrow : ∀ row ∈ rows, row.length = k * m') :
    (level k r rows).length = m ∧ ∀ a < m, ((level k r rows).getD a []).length = m' ∧
      ∀ b < m', ent (level k r rows) a b =
        ∑ c ∈ range k, ∑ e ∈ range k, ent r c e * ent rows (a * k + c) (b * k + e) := by
  obtain ⟨hc1, hc2⟩ := chunks_spec k hk m rows.length rows hl (by rw [hl]; nlinarith)
  refine ⟨by simp [level, hc1], fun a ha => ?_⟩
  have ha' : a < (chunks k rows.length rows).length := hc1 ▸ ha
  have hgrp := hc2 a ha
  set grp := (chunks k rows.length rows).getD a [] with hgrpdef
  have hgl : grp.length = k := by
    rw [hgrp, List.length_take, List.length_drop, hl]
    have : a * k + k ≤ k * m := by nlinarith
    omega
  have hgrow : ∀ row ∈ grp, row.length = k * m' := by
    intro row hrow'
    rw [hgrp] at hrow'
    exact hrow _ (List.mem_of_mem_drop (List.mem_of_mem_take hrow'))
  have hgent : ∀ c < k, ∀ j, ent grp c j = ent rows (a * k + c) j := by
    intro c hc j
    simp only [ent, hgrp, getD_take_drop rows (a * k) k c hc]
  obtain ⟨h1, h2⟩ := level_row_spec k m' hk r grp hr hrc hgl hgrow
  have hla : (level k r rows).getD a [] =
      sumRows (List.zipWith (fun row rc => (chunks k row.length row).map fun bg => dot rc bg) grp r) := by
    simp [level, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ha', hgrpdef,
      List.getD_eq_getElem _ [] ha']
  refine ⟨by rw [hla, h1], fun b hb => ?_⟩
  rw [ent, hla, h2 b hb]
  exact sum_congr rfl fun c hc => sum_congr rfl fun e _ => by rw [hgent c (mem_range.mp hc)]

/-! ### `yRows`: the rows of `B_l X B_rᵀ`, packed -/

theorem getD_map_zero {α : Type} (f : α → ℤ) (L : List α) (d : α) (hd : f d = 0) (i : ℕ) :
    (L.map f).getD i 0 = f (L.getD i d) := by
  rw [← hd, getD_map_list]

theorem yRows_spec (k w n : ℕ) (X Bl Br : List (List ℤ)) (hX : X.length = k)
    (hXr : ∀ r ∈ X, r.length = k) (hBr : Br.length = n) (hBrr : ∀ r ∈ Br, r.length = k) :
    (yRows k w X Bl Br).length = Bl.length ∧ ∀ i, (∀ r ∈ Bl, r.length = k) →
      (yRows k w X Bl Br).getD i 0 = ∑ j ∈ range n,
        (∑ p ∈ range k, ∑ q ∈ range k, ent Bl i p * ent X p q * ent Br j q) * 2 ^ (w * j) := by
  obtain ⟨hc1, hc2⟩ := colPack_spec k w Br hBrr
  set Bc := colPack k w Br
  set Z := X.map fun row => dot row Bc with hZ
  have hZp : ∀ p, Z.getD p 0 = ∑ q ∈ range k, ent X p q * ∑ j ∈ range n, ent Br j q * 2 ^ (w * j) := by
    intro p
    rw [hZ, getD_map_zero _ X [] (by rfl)]
    by_cases hp : p < X.length
    · have hlen : (X.getD p []).length = k :=
        hXr _ (by simp [List.getD_eq_getElem?_getD, hp, List.getElem_mem])
      rw [dot_eq, hlen]
      refine sum_congr rfl fun q hq => ?_
      rw [hc2 q (mem_range.mp hq), hBr]
      rfl
    · have : X.getD p [] = [] := by simp [List.getD_eq_getElem?_getD, hp]
      have h0 : ∀ q, ent X p q = 0 := fun q => by simp only [ent, this, List.getD_nil]
      simp only [this, h0, zero_mul, sum_const_zero]
      rfl
  refine ⟨by simp [yRows], fun i hBl => ?_⟩
  have hR : (yRows k w X Bl Br).getD i 0 = dot (Bl.getD i []) Z := by
    simp only [yRows]
    exact getD_map_zero _ Bl [] (by rfl) i
  rw [hR]
  have hexp : ∀ len, (∀ p ∈ range len, p < k ∨ ent Bl i p = 0) → len = k →
      ∑ p ∈ range len, (Bl.getD i []).getD p 0 * Z.getD p 0 = ∑ j ∈ range n,
        (∑ p ∈ range k, ∑ q ∈ range k, ent Bl i p * ent X p q * ent Br j q) * 2 ^ (w * j) := by
    intro len _ hlen
    subst hlen
    simp only [hZp, mul_sum, sum_mul]
    calc ∑ p ∈ range len, ∑ q ∈ range len, ∑ j ∈ range n,
            (Bl.getD i []).getD p 0 * (ent X p q * (ent Br j q * 2 ^ (w * j)))
        = ∑ p ∈ range len, ∑ j ∈ range n, ∑ q ∈ range len,
            (Bl.getD i []).getD p 0 * (ent X p q * (ent Br j q * 2 ^ (w * j))) :=
          sum_congr rfl fun p _ => sum_comm
      _ = ∑ j ∈ range n, ∑ p ∈ range len, ∑ q ∈ range len,
            (Bl.getD i []).getD p 0 * (ent X p q * (ent Br j q * 2 ^ (w * j))) := sum_comm
      _ = _ := by
          refine sum_congr rfl fun j _ => sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
          simp only [ent]; ring
  by_cases hi : i < Bl.length
  · have hlen : (Bl.getD i []).length = k :=
      hBl _ (by simp [List.getD_eq_getElem?_getD, hi, List.getElem_mem])
    rw [dot_eq, hlen]
    exact hexp k (fun p hp => Or.inl (mem_range.mp hp)) rfl
  · have : Bl.getD i [] = [] := by simp [List.getD_eq_getElem?_getD, hi]
    have h0 : ∀ p, ent Bl i p = 0 := fun p => by simp only [ent, this, List.getD_nil]
    simp only [this, dot, h0, zero_mul, sum_const_zero]

/-! ### Bounded packings -/

/-- `4 |∑_{r<N} d_r B^r| < B^N` when every `|d_r| ≤ D` and `4 (D + 1) ≤ B`. -/
theorem packed_bound (B D : ℤ) (hB : 4 * (D + 1) ≤ B) (hD : 0 ≤ D) (d : ℕ → ℤ) :
    ∀ N, (∀ r < N, |d r| ≤ D) → 4 * |∑ r ∈ range N, d r * B ^ r| < B ^ N
  | 0, _ => by simp
  | N + 1, hd => by
    have ih := packed_bound B D hB hD d N fun r hr => hd r (by omega)
    have hBp : 0 < B ^ N := pow_pos (by omega) N
    rw [sum_range_succ, pow_succ]
    have h1 := abs_add_le (∑ r ∈ range N, d r * B ^ r) (d N * B ^ N)
    rw [abs_mul, abs_of_pos hBp] at h1
    have h2 := hd N (by omega)
    nlinarith

/-- Two balanced packings in base `B` with digits `4 |·| < B` agree digit by digit. -/
theorem digits_unique (B : ℤ) (hB : 1 ≤ B) (a b : ℕ → ℤ) (N : ℕ) (ha : ∀ j < N, 4 * |a j| < B)
    (hb : ∀ j < N, 4 * |b j| < B) (h : ∑ j ∈ range N, a j * B ^ j = ∑ j ∈ range N, b j * B ^ j) :
    ∀ j < N, a j = b j := by
  have h0 : ∑ j ∈ range N, (a j - b j) * B ^ j = 0 := by
    simp only [sub_mul, sum_sub_distrib, h, sub_self]
  intro j hj
  have := digits_eq_zero B hB (fun j => a j - b j) N (fun j hj => by
    have h1 := ha j hj; have h2 := hb j hj
    have := abs_sub (a j) (b j)
    linarith) h0 j hj
  linarith

/-- Splitting a sum over `range (m k)` into blocks of `k`. -/
theorem sum_range_blocks (f : ℕ → ℤ) (k : ℕ) : ∀ m, ∑ x ∈ range (m * k), f x =
    ∑ u ∈ range m, ∑ r ∈ range k, f (u * k + r)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_range_blocks f k m, sum_range_succ]

/-- The rounding read-out of the top digit. -/
theorem decodeTop_eq (w k : ℕ) (hw : 1 ≤ w) (hk : 2 ≤ k) (t J : ℤ)
    (hJ : 4 * |J| < 2 ^ ((k - 1) * w)) :
    decodeTop w k (t * 2 ^ ((k - 1) * w) + J) = t := by
  have hkw : 1 ≤ (k - 1) * w := Nat.one_le_iff_ne_zero.mpr (by
    have : 1 ≤ k - 1 := by omega
    positivity)
  have hM : (2 : ℤ) ^ ((k - 1) * w) = 2 * 2 ^ ((k - 1) * w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hk1 : ¬ k ≤ 1 := by omega
  simp only [decodeTop, hk1, if_false, pow2_eq]
  set M := (2 : ℤ) ^ ((k - 1) * w)
  set H := (2 : ℤ) ^ ((k - 1) * w - 1)
  have hHp : 0 < H := pow_pos (by norm_num) _
  rw [show t * M + J + H = (J + H) + t * M by ring, Int.add_mul_ediv_right _ _ (by positivity)]
  have hJ' := abs_lt.mp (show |J| < H by nlinarith [abs_nonneg J])
  rw [Int.ediv_eq_zero_of_lt (by linarith) (by linarith), zero_add]

/-! ### The first level -/

theorem sum_shift_ind (h : ℕ → ℤ) (n e N : ℕ) (hN : n + e ≤ N) :
    ∑ pos ∈ range N, (if e ≤ pos ∧ pos - e < n then h pos else 0) = ∑ j ∈ range n, h (j + e) := by
  rw [← sum_filter]
  have hset : (range N).filter (fun pos => e ≤ pos ∧ pos - e < n) = (range n).map (addRightEmbedding e) := by
    ext pos
    simp only [mem_filter, mem_range, mem_map, addRightEmbedding_apply]
    constructor
    · rintro ⟨_, h2, h3⟩
      exact ⟨pos - e, h3, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hset, sum_map]
  rfl

/-- The digits of a product of packings. -/
def convDig (n k : ℕ) (a b : ℕ → ℤ) (pos : ℕ) : ℤ :=
  ∑ e ∈ range k, if e ≤ pos ∧ pos - e < n then b e * a (pos - e) else 0

theorem conv_eq (n k : ℕ) (a b : ℕ → ℤ) (B : ℤ) :
    (∑ j ∈ range n, a j * B ^ j) * (∑ e ∈ range k, b e * B ^ e) =
      ∑ pos ∈ range (n + k), convDig n k a b pos * B ^ pos := by
  have hin : ∀ e ∈ range k, ∑ pos ∈ range (n + k),
      (if e ≤ pos ∧ pos - e < n then b e * a (pos - e) else 0) * B ^ pos =
      ∑ j ∈ range n, a j * B ^ j * (b e * B ^ e) := by
    intro e he
    have := sum_shift_ind (fun pos => b e * a (pos - e) * B ^ pos) n e (n + k)
      (by have := mem_range.mp he; omega)
    simp only [ite_mul, zero_mul]
    rw [this]
    refine sum_congr rfl fun j _ => ?_
    simp only [Nat.add_sub_cancel]
    rw [pow_add]; ring
  simp only [convDig, sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  exact (sum_congr rfl hin).symm

theorem getD_reverse_eq (l : List ℤ) (e : ℕ) (he : e < l.length) :
    l.reverse.getD e 0 = l.getD (l.length - 1 - e) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse he]

theorem mapM_option_spec {α β : Type} (f : α → Option β) (d : β) :
    ∀ (l : List α) (L : List β), l.mapM f = some L →
      L.length = l.length ∧ ∀ i (hi : i < l.length), f (l[i]) = some (L.getD i d)
  | [], L, h => by
    simp at h; subst h; exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | x :: xs, L, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨ih1, ih2⟩ := mapM_option_spec f d xs bs hxs
        refine ⟨by simp [ih1], fun i hi => ?_⟩
        cases i with
        | zero => simpa using hx
        | succ i => simpa using ih2 i (by simpa using hi)


/-- Reading the top digit of a bounded packing of `k ≥ 1` digits. -/
theorem decodeTop_sum (w k : ℕ) (hw : 1 ≤ w) (hk : 1 ≤ k) (dig : ℕ → ℤ) (D : ℤ) (hD0 : 0 ≤ D)
    (hD : ∀ r, |dig r| ≤ D) (hwb : 4 * (D + 1) ≤ 2 ^ w) :
    decodeTop w k (∑ r ∈ range k, dig r * ((2 : ℤ) ^ w) ^ r) = dig (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos k' with hk0 | hkpos
  · subst hk0
    simp [decodeTop]
  · rw [sum_range_succ, ← pow_mul, mul_comm w k',
      add_comm (∑ r ∈ range k', dig r * ((2 : ℤ) ^ w) ^ r)]
    have hJ := packed_bound (2 ^ w) D hwb hD0 dig k' (fun r _ => hD r)
    rw [← pow_mul, mul_comm w k'] at hJ
    have := decodeTop_eq w (k' + 1) hw (by omega) (dig k') (∑ r ∈ range k', dig r * ((2 : ℤ) ^ w) ^ r)
      (by rw [Nat.add_sub_cancel]; exact hJ)
    rwa [Nat.add_sub_cancel] at this

theorem qpoly_eq (w k : ℕ) (r : List ℤ) (hr : r.length = k) :
    pk w r.reverse = ∑ e ∈ range k, r.getD (k - 1 - e) 0 * ((2 : ℤ) ^ w) ^ e := by
  rw [pk_eq, List.length_reverse, hr]
  refine sum_congr rfl fun e he => ?_
  rw [getD_reverse_eq r e (by rw [hr]; exact mem_range.mp he), hr, ← pow_mul]

/-- The super-digits of the first-level product. -/
def l1Dig (k n : ℕ) (T : List (List ℤ)) (y : ℕ → ℕ → ℤ) (pos : ℕ) : ℤ :=
  ∑ c ∈ range k, convDig n k (y c) (fun e => ent T c (k - 1 - e)) pos

theorem l1Dig_bound (k n : ℕ) (T : List (List ℤ)) (y : ℕ → ℕ → ℤ) (tm ym : ℤ)
    (htm : ∀ c e, |ent T c e| ≤ tm) (hym : ∀ c j, |y c j| ≤ ym) (htm0 : 0 ≤ tm) (pos : ℕ) :
    |l1Dig k n T y pos| ≤ k * k * tm * ym := by
  unfold l1Dig convDig
  have hterm : ∀ c e, |(if e ≤ pos ∧ pos - e < n then ent T c (k - 1 - e) * y c (pos - e) else 0)| ≤
      tm * ym := by
    intro c e
    split_ifs
    · rw [abs_mul]; exact mul_le_mul (htm _ _) (hym _ _) (abs_nonneg _) htm0
    · simp only [abs_zero]; exact mul_nonneg htm0 ((abs_nonneg _).trans (hym 0 0))
  calc |∑ c ∈ range k, ∑ e ∈ range k, _| ≤ ∑ c ∈ range k, ∑ e ∈ range k, tm * ym := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => ?_)
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => hterm c e)
    _ = k * k * tm * ym := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

theorem l1Row_spec (w k m bnd : ℕ) (hw : 1 ≤ w) (hk : 1 ≤ k) (T : List (List ℤ)) (hT : T.length = k)
    (hTr : ∀ r ∈ T, r.length = k) (grp : List ℤ) (hg : grp.length = k)
    (y : ℕ → ℕ → ℤ) (hy : ∀ c < k, grp.getD c 0 = ∑ j ∈ range (k * m), y c j * 2 ^ (w * j))
    (tm ym : ℤ) (htm : ∀ c e, |ent T c e| ≤ tm) (hym : ∀ c j, |y c j| ≤ ym) (htm0 : 0 ≤ tm)
    (hym0 : 0 ≤ ym) (hwb : 4 * (k * k * tm * ym + 1) ≤ 2 ^ w) (hbnd : 4 * (bnd : ℤ) < 2 ^ (k * w))
    (L : List ℤ) (h : l1Row w k m bnd (T.map fun r => pk w r.reverse) grp = some L) :
    L.length = m ∧ ∀ u < m, L.getD u 0 = ∑ c ∈ range k, ∑ e ∈ range k, ent T c e * y c (u * k + e) := by
  set B : ℤ := 2 ^ w with hB
  have hB4 : 4 ≤ B := by
    have : 0 ≤ k * k * tm * ym := by positivity
    linarith
  set qs := T.map fun r => pk w r.reverse with hqs
  set P := dot grp qs with hP
  set S := unpk (k * w) (m + 1) P with hS
  have hSl : S.length = m + 1 := unpk_length _ _ _
  simp only [l1Row, ← hP, ← hS] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hpk, hbd⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  -- the product as a packing of digits
  have hqc : ∀ c < k, qs.getD c 0 = ∑ e ∈ range k, ent T c (k - 1 - e) * B ^ e := by
    intro c hc
    have hc' : c < T.length := hT ▸ hc
    rw [hqs, getD_map_zero _ T [] (by rfl)]
    have hlen : (T.getD c []).length = k := hTr _ (by simp [List.getD_eq_getElem?_getD, hc', List.getElem_mem])
    rw [qpoly_eq w k _ hlen]
    rfl
  have hPdig : P = ∑ pos ∈ range ((m + 1) * k), l1Dig k (k * m) T y pos * B ^ pos := by
    rw [hP, dot_eq, hg, show (m + 1) * k = k * m + k by ring]
    have : ∀ c ∈ range k, grp.getD c 0 * qs.getD c 0 = ∑ pos ∈ range (k * m + k),
        convDig (k * m) k (y c) (fun e => ent T c (k - 1 - e)) pos * B ^ pos := by
      intro c hc
      rw [hy c (mem_range.mp hc), hqc c (mem_range.mp hc), ← conv_eq]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [hB, ← pow_mul]
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun pos _ => ?_
    rw [l1Dig, sum_mul]
  set s : ℕ → ℤ := fun u => ∑ r ∈ range k, l1Dig k (k * m) T y (u * k + r) * B ^ r with hs
  have hPs : P = ∑ u ∈ range (m + 1), s u * (B ^ k) ^ u := by
    rw [hPdig, sum_range_blocks]
    refine sum_congr rfl fun u _ => ?_
    rw [hs, sum_mul]
    refine sum_congr rfl fun r _ => ?_
    simp only [hB, ← pow_mul]
    rw [mul_assoc, ← pow_add]
    congr 2
    ring
  have hD := l1Dig_bound k (k * m) T y tm ym htm hym htm0
  have hs4 : ∀ u, 4 * |s u| < B ^ k := fun u =>
    packed_bound B (k * k * tm * ym) hwb (by positivity) (fun r => l1Dig k (k * m) T y (u * k + r)) k
      (fun r _ => hD _)
  have hSk : ∀ u, 4 * |S.getD u 0| < B ^ k := by
    intro u
    have h1 : |S.getD u 0| ≤ bnd := boundedBy_spec bnd S hbd u
    rw [hB, ← pow_mul, mul_comm w k]
    linarith
  have hSs : ∀ u < m + 1, S.getD u 0 = s u := by
    have hpk' : ∑ u ∈ range (m + 1), S.getD u 0 * (B ^ k) ^ u = ∑ u ∈ range (m + 1), s u * (B ^ k) ^ u := by
      rw [← hPs, ← hpk, pk_eq, hSl]
      refine sum_congr rfl fun u _ => ?_
      rw [hB, ← pow_mul, ← pow_mul]
      congr 2; ring
    exact digits_unique (B ^ k) (one_le_pow₀ (by linarith)) (fun u => S.getD u 0) s (m + 1)
      (fun u _ => hSk u) (fun u _ => hs4 u) hpk'
  refine ⟨by simp [hSl], fun u hu => ?_⟩
  have hu' : u < (S.take m).length := by simp [hSl, hu]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hu', Option.map_some,
    Option.getD_some, List.getElem_take, ← List.getD_eq_getElem _ 0, hSs u (by omega)]
  -- the top digit
  have htop : l1Dig k (k * m) T y (u * k + (k - 1)) =
      ∑ c ∈ range k, ∑ e ∈ range k, ent T c e * y c (u * k + e) := by
    unfold l1Dig convDig
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_range_reflect]
    refine sum_congr rfl fun e he => ?_
    have he' := mem_range.mp he
    have hukm : u * k + k ≤ k * m := by
      have := Nat.mul_le_mul_right k (show u + 1 ≤ m from hu)
      rw [Nat.add_mul, one_mul, Nat.mul_comm m k] at this
      exact this
    rw [if_pos ⟨by omega, by omega⟩]
    beta_reduce
    rw [show k - 1 - (k - 1 - e) = e by omega,
      show u * k + (k - 1) - (k - 1 - e) = u * k + e by omega]
  rw [← htop]
  have := decodeTop_sum w k hw hk (fun r => l1Dig k (k * m) T y (u * k + r)) (k * k * tm * ym)
    (by positivity) (fun r => hD _) hwb
  simpa [hs, hB] using this

theorem level1C_spec (w k n1 bnd : ℕ) (hw : 1 ≤ w) (hk : 1 ≤ k) (T : List (List ℤ)) (hT : T.length = k)
    (hTr : ∀ r ∈ T, r.length = k) (rows : List ℤ) (hrows : rows.length = k * n1)
    (y : ℕ → ℕ → ℤ) (hy : ∀ i < k * n1, rows.getD i 0 = ∑ j ∈ range (k * n1), y i j * 2 ^ (w * j))
    (tm ym : ℤ) (htm : ∀ c e, |ent T c e| ≤ tm) (hym : ∀ i j, |y i j| ≤ ym) (htm0 : 0 ≤ tm)
    (hym0 : 0 ≤ ym) (hwb : 4 * (k * k * tm * ym + 1) ≤ 2 ^ w) (hbnd : 4 * (bnd : ℤ) < 2 ^ (k * w))
    (L : List (List ℤ)) (h : level1C w k n1 bnd T rows = some L) :
    L.length = n1 ∧ ∀ a < n1, (L.getD a []).length = n1 ∧ ∀ u < n1,
      ent L a u = ∑ c ∈ range k, ∑ e ∈ range k, ent T c e * y (a * k + c) (u * k + e) := by
  obtain ⟨hc1, hc2⟩ := chunks_spec k hk n1 rows.length rows hrows (by rw [hrows]; nlinarith)
  obtain ⟨hm1, hm2⟩ := mapM_option_spec _ [] _ L h
  refine ⟨by rw [hm1, hc1], fun a ha => ?_⟩
  have ha' : a < (chunks k rows.length rows).length := hc1 ▸ ha
  have hl1 := hm2 a ha'
  rw [← List.getD_eq_getElem _ [] ha', hc2 a ha] at hl1
  have hgl : ((rows.drop (a * k)).take k).length = k := by
    rw [List.length_take, List.length_drop, hrows]
    have : a * k + k ≤ k * n1 := by
      have := Nat.mul_le_mul_right k (show a + 1 ≤ n1 from ha)
      rw [Nat.add_mul, one_mul, Nat.mul_comm n1 k] at this
      exact this
    omega
  have hgy : ∀ c < k, ((rows.drop (a * k)).take k).getD c 0 =
      ∑ j ∈ range (k * n1), y (a * k + c) j * 2 ^ (w * j) := by
    intro c hc
    rw [getD_take_drop rows (a * k) k c hc]
    have : a * k + c < k * n1 := by
      have := Nat.mul_le_mul_right k (show a + 1 ≤ n1 from ha)
      rw [Nat.add_mul, one_mul, Nat.mul_comm n1 k] at this
      omega
    exact hy _ this
  obtain ⟨hr1, hr2⟩ := l1Row_spec w k n1 bnd hw hk T hT hTr _ hgl (fun c j => y (a * k + c) j) hgy
    tm ym htm (fun c j => hym _ _) htm0 hym0 hwb hbnd _ hl1
  exact ⟨hr1, fun u hu => hr2 u hu⟩

/-! ### `permY` -/

theorem permRows_spec (idx : List ℕ) (Y : List (List ℤ)) :
    (permRows idx Y).length = idx.length ∧
      ∀ a < idx.length, (permRows idx Y).getD a [] = Y.getD (idx.getD a 0) [] := by
  refine ⟨by simp [permRows], fun a ha => ?_⟩
  simp [permRows, List.getD_eq_getElem?_getD, List.getElem?_map, ha, nth_eq_getD]

theorem transp_row_length (k : ℕ) : ∀ (L : List (List ℤ)), (∀ r ∈ L, r.length = k) →
    ∀ r ∈ transp k L, r.length = L.length
  | [], _ => by
    intro r hr
    simp only [transp, List.mem_replicate] at hr
    rw [hr.2]; rfl
  | x :: xs, hlen => by
    intro r hr
    have hx : x.length = k := hlen x (by simp)
    have ih := transp_row_length k xs fun r' hr' => hlen r' (by simp [hr'])
    simp only [transp] at hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    rw [List.getElem_zipWith, List.length_cons, List.length_cons, ih _ (List.getElem_mem _)]

theorem permRows_rows (idx : List ℕ) (Y : List (List ℤ)) (n : ℕ) (hY : ∀ r ∈ Y, r.length = n)
    (hYl : ∀ i ∈ idx, i < Y.length) : ∀ r ∈ permRows idx Y, r.length = n := by
  obtain ⟨p1, p2⟩ := permRows_spec idx Y
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hr
  rw [← List.getD_eq_getElem _ [] ha, p2 a (p1 ▸ ha)]
  have hi : idx.getD a 0 < Y.length := hYl _ (by
    rw [List.getD_eq_getElem _ 0 (p1 ▸ ha)]; exact List.getElem_mem _)
  exact hY _ (by rw [List.getD_eq_getElem _ [] hi]; exact List.getElem_mem _)

theorem permY_spec (n : ℕ) (idx : List ℕ) (Y : List (List ℤ)) (hidx : idx.length = n)
    (hYn : Y.length = n) (hY : ∀ r ∈ Y, r.length = n) (hYl : ∀ i ∈ idx, i < n) :
    (permY n idx Y).length = n ∧ (∀ r ∈ permY n idx Y, r.length = n) ∧
      ∀ a < n, ∀ b < n, ent (permY n idx Y) a b = ent Y (idx.getD a 0) (idx.getD b 0) := by
  set A := permRows idx Y with hA
  obtain ⟨a1, a2⟩ := permRows_spec idx Y
  have aR := permRows_rows idx Y n hY (fun i hi => hYn ▸ hYl i hi)
  set Bm := transp n A with hBm
  obtain ⟨b1, b2⟩ := transp_spec n A aR
  have bR : ∀ r ∈ Bm, r.length = n := by
    intro r hr; rw [transp_row_length n A aR r hr, a1, hidx]
  set C := permRows idx Bm with hC
  obtain ⟨c1, c2⟩ := permRows_spec idx Bm
  have cR := permRows_rows idx Bm n bR (fun i hi => b1 ▸ hYl i hi)
  obtain ⟨d1, d2⟩ := transp_spec n C cR
  refine ⟨d1, fun r hr => by rw [transp_row_length n C cR r hr, c1, hidx], fun a ha b hb => ?_⟩
  show ((transp n C).getD a []).getD b 0 = _
  have hib : idx.getD b 0 < n := hYl _ (by
    rw [List.getD_eq_getElem _ 0 (hidx ▸ hb)]; exact List.getElem_mem _)
  rw [d2 a ha b, c2 b (hidx ▸ hb), hBm, b2 _ hib a, a2 a (hidx ▸ ha)]
  rfl

/-! ### Tables and the last level -/

theorem foldl_add_eq_sum : ∀ (l : List ℤ) (a : ℤ), l.foldl (· + ·) a = a + ∑ i ∈ range l.length, l.getD i 0
  | [], a => by simp
  | x :: xs, a => by
    rw [List.foldl_cons, foldl_add_eq_sum xs, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The value of a position code: `0` if not selected, `v 2^(st q)` for code `q + 1`. -/
def pcode (st : ℕ) (v : ℤ) : ℕ → ℤ
  | 0 => 0
  | q + 1 => v * 2 ^ (st * q)

theorem ptab_spec (st : ℕ) (pos : List ℕ) (col : List ℤ) (hp : pos.length = 24) (hc : col.length = 24) :
    ptab st pos col = ∑ m ∈ range 24, pcode st (col.getD m 0) (pos.getD m 0) := by
  rw [ptab, foldl_add_eq_sum, zero_add, List.length_zipWith, hp, hc, min_self]
  refine sum_congr rfl fun m hm => ?_
  have hm1 : m < col.length := hc ▸ mem_range.mp hm
  have hm2 : m < pos.length := hp ▸ mem_range.mp hm
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hm1,
    List.getElem?_eq_getElem hm2, List.getD_eq_getElem _ 0 hm1, List.getD_eq_getElem _ 0 hm2]
  simp only [Option.getD_some]
  cases pos[m] <;> simp [pcode, pow2_eq]

theorem flatten_getD (k : ℕ) : ∀ (M : List (List ℤ)), (∀ r ∈ M, r.length = k) →
    (M.flatten).length = k * M.length ∧ ∀ c < M.length, ∀ e < k, (M.flatten).getD (c * k + e) 0 = ent M c e
  | [], _ => ⟨by simp, fun c hc => absurd hc (by simp)⟩
  | r :: rs, hl => by
    have hr := hl r (by simp)
    obtain ⟨ih1, ih2⟩ := flatten_getD k rs fun r' hr' => hl r' (by simp [hr'])
    refine ⟨by simp [hr, ih1, Nat.mul_succ, add_comm], fun c hc e he => ?_⟩
    rw [List.flatten_cons]
    cases c with
    | zero =>
      simp only [zero_mul, zero_add, ent, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    | succ c =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hr]; nlinarith), hr,
        show (c + 1) * k + e - k = c * k + e by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD,
        ih2 c (by simpa using hc) e he]
      simp [ent]

theorem cols_spec (k : ℕ) (rho : List (List (List ℤ))) (hl : rho.length = 24)
    (hm : ∀ M ∈ rho, M.length = k ∧ ∀ r ∈ M, r.length = k) :
    (cols k rho).length = k * k ∧ (∀ r ∈ cols k rho, r.length = 24) ∧
      ∀ c < k, ∀ e < k, ∀ m, ((cols k rho).getD (c * k + e) []).getD m 0 = ent (rho.getD m []) c e := by
  have hfl : ∀ r ∈ rho.map List.flatten, r.length = k * k := by
    intro r hr
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hr
    rw [(flatten_getD k M (hm M hM).2).1, (hm M hM).1]
  obtain ⟨t1, t2⟩ := transp_spec (k * k) _ hfl
  refine ⟨t1, fun r hr => by rw [transp_row_length _ _ hfl r hr, List.length_map, hl], fun c hc e he m => ?_⟩
  have hce : c * k + e < k * k := by nlinarith
  rw [cols, t2 _ hce m]
  by_cases hmr : m < rho.length
  · have hgm := getD_map_list List.flatten rho [] m
    simp only [List.flatten_nil] at hgm
    rw [hgm]
    have hM := hm (rho.getD m []) (by rw [List.getD_eq_getElem _ [] hmr]; exact List.getElem_mem _)
    exact (flatten_getD k _ hM.2).2 c (by rw [hM.1]; exact hc) e he
  · have : rho.getD m [] = [] := by simp [List.getD_eq_getElem?_getD, hmr]
    have h2 : (rho.map List.flatten).getD m [] = [] := by simp [List.getD_eq_getElem?_getD, hmr]
    rw [h2, this]; simp [ent]

theorem rtabP_spec (k st : ℕ) (hk : 0 < k) (cs : List (List ℤ)) (pos : List ℕ) (hcs : cs.length = k * k) :
    (rtabP k st cs pos).length = k ∧ (∀ r ∈ rtabP k st cs pos, r.length = k) ∧
      ∀ c < k, ∀ e < k, ent (rtabP k st cs pos) c e = ptab st pos (cs.getD (c * k + e) []) := by
  have hl : (cs.map (ptab st pos)).length = k * k := by rw [List.length_map, hcs]
  obtain ⟨c1, c2⟩ := chunks_spec k hk k (k * k) (cs.map (ptab st pos)) hl (by nlinarith)
  refine ⟨c1, fun r hr => ?_, fun c hc e he => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hr
    rw [← List.getD_eq_getElem _ [] ha]
    show ((chunks k (k * k) (cs.map (ptab st pos))).getD a []).length = k
    rw [c2 a (c1 ▸ ha), List.length_take, List.length_drop, hl]
    have : a * k + k ≤ k * k := by
      have := Nat.mul_le_mul_right k (show a + 1 ≤ k from c1 ▸ ha)
      rw [Nat.add_mul, one_mul] at this; exact this
    omega
  · rw [ent, rtabP, c2 c hc, getD_take_drop _ _ _ _ he, mul_comm c k,
      show k * c + e = c * k + e by ring]
    exact getD_map_zero (ptab st pos) cs [] (by simp [ptab]) (c * k + e)

theorem frob_spec (k : ℕ) (M V : List (List ℤ)) (hM : M.length = k) (hMr : ∀ r ∈ M, r.length = k)
    (hV : V.length = k) :
    frob M V = ∑ c ∈ range k, ∑ e ∈ range k, ent M c e * ent V c e := by
  rw [frob, foldl_add_eq_sum, zero_add, List.length_zipWith, hM, hV, min_self]
  refine sum_congr rfl fun c hc => ?_
  have hc1 : c < M.length := hM ▸ mem_range.mp hc
  have hc2 : c < V.length := hV ▸ mem_range.mp hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hc1,
    List.getElem?_eq_getElem hc2]
  simp only [Option.getD_some]
  rw [dot_eq, hMr _ (List.getElem_mem hc1)]
  refine sum_congr rfl fun e _ => ?_
  simp [ent, List.getElem?_eq_getElem hc1, List.getElem?_eq_getElem hc2]

theorem finalP_spec (st : ℕ) (rho0 : List (List (List ℤ))) (pos : List ℕ) (V : List (List ℤ))
    (hr : rho0.length = 24) (hp : pos.length = 24) :
    finalP st rho0 pos V = ∑ m ∈ range 24, pcode st (frob (rho0.getD m []) V) (pos.getD m 0) := by
  rw [finalP, foldl_add_eq_sum, zero_add, List.length_zipWith, hr, hp, min_self]
  refine sum_congr rfl fun m hm => ?_
  have hm1 : m < rho0.length := hr ▸ mem_range.mp hm
  have hm2 : m < pos.length := hp ▸ mem_range.mp hm
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hm1,
    List.getElem?_eq_getElem hm2, List.getD_eq_getElem _ [] hm1, List.getD_eq_getElem _ 0 hm2]
  simp only [Option.getD_some]
  cases pos[m] <;> simp [pcode, pow2_eq]

/-- **The last three levels.** `tensorP3` on an `(k₀k₁k₂)²` matrix `L`. -/
theorem tensorP3_spec (β s1 k0 k1 k2 : ℕ) (h0 : 0 < k0) (h1 : 0 < k1) (h2 : 0 < k2)
    (rho0 : List (List (List ℤ))) (hr0 : rho0.length = 24)
    (hr0m : ∀ M ∈ rho0, M.length = k0 ∧ ∀ r ∈ M, r.length = k0)
    (cs1 cs2 : List (List ℤ)) (hc1 : cs1.length = k1 * k1) (hc2 : cs2.length = k2 * k2)
    (p0 p1 p2 : List ℕ) (hp0 : p0.length = 24) (L : List (List ℤ)) (hL : L.length = k0 * k1 * k2)
    (hLr : ∀ r ∈ L, r.length = k0 * k1 * k2) :
    tensorP3 β s1 [k0, k1, k2] rho0 [cs1, cs2] [p0, p1, p2] L =
      ∑ m ∈ range 24, pcode (β * 24 * s1) (∑ c0 ∈ range k0, ∑ e0 ∈ range k0, ent (rho0.getD m []) c0 e0 *
        ∑ c1 ∈ range k1, ∑ e1 ∈ range k1, ptab (β * s1) p1 (cs1.getD (c1 * k1 + e1) []) *
          ∑ c2 ∈ range k2, ∑ e2 ∈ range k2, ptab β p2 (cs2.getD (c2 * k2 + e2) []) *
            ent L ((c0 * k1 + c1) * k2 + c2) ((e0 * k1 + e1) * k2 + e2)) (p0.getD m 0) := by
  obtain ⟨t2l, t2r, t2e⟩ := rtabP_spec k2 β h2 cs2 p2 hc2
  obtain ⟨t1l, t1r, t1e⟩ := rtabP_spec k1 (β * s1) h1 cs1 p1 hc1
  set V2 := level k2 (rtabP k2 β cs2 p2) L
  obtain ⟨v2l, v2s⟩ := level_spec k2 (k0 * k1) (k0 * k1) h2 _ L t2l t2r (by rw [hL]; ring)
    (fun r hr => by rw [hLr r hr]; ring)
  have v2r : ∀ r ∈ V2, r.length = k1 * k0 := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hr
    rw [← List.getD_eq_getElem _ [] ha, (v2s a (v2l ▸ ha)).1]; ring
  set V := level k1 (rtabP k1 (β * s1) cs1 p1) V2
  obtain ⟨vl, vs⟩ := level_spec k1 k0 k0 h1 _ V2 t1l t1r (by rw [v2l]; ring) v2r
  have hT : tensorP3 β s1 [k0, k1, k2] rho0 [cs1, cs2] [p0, p1, p2] L = finalP (β * 24 * s1) rho0 p0 V := rfl
  rw [hT, finalP_spec _ _ _ _ hr0 hp0]
  refine sum_congr rfl fun m hm => ?_
  congr 1
  have hM := hr0m (rho0.getD m []) (by
    rw [List.getD_eq_getElem _ [] (hr0 ▸ mem_range.mp hm)]; exact List.getElem_mem _)
  rw [frob_spec k0 _ V hM.1 hM.2 vl]
  refine sum_congr rfl fun c0 hc0 => sum_congr rfl fun e0 he0 => ?_
  congr 1
  rw [(vs c0 (mem_range.mp hc0)).2 e0 (mem_range.mp he0)]
  refine sum_congr rfl fun c1 hc1' => sum_congr rfl fun e1 he1 => ?_
  rw [t1e c1 (mem_range.mp hc1') e1 (mem_range.mp he1)]
  congr 1
  have ha : c0 * k1 + c1 < k0 * k1 := by
    have := mem_range.mp hc0; have := mem_range.mp hc1'; nlinarith
  have hb : e0 * k1 + e1 < k0 * k1 := by
    have := mem_range.mp he0; have := mem_range.mp he1; nlinarith
  rw [(v2s _ ha).2 _ hb]
  refine sum_congr rfl fun c2 hc2' => sum_congr rfl fun e2 he2 => ?_
  rw [t2e c2 (mem_range.mp hc2') e2 (mem_range.mp he2)]

end LayerDProto
