import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.StarOrdered
import LayerDProto.Packed

/-!
# Soundness of the packed positive-definiteness checker

`posDef_of_checkPD`: if `checkPD k β w a c A W e = true` (evaluated by the kernel), then the real
matrix read from the list `A` is positive definite. The proof:

1. the packed row identities give `∑ⱼ ((W A Wᵀ)ᵢⱼ - [i = j] eᵢ) Bʲ = 0` with `B = 2^β`;
2. every digit is bounded by `k² w² a + c < B / 2`, so every digit is zero (`digits_eq_zero`),
   i.e. `W A Wᵀ = diag e` over `ℤ`;
3. `W` is lower triangular with positive diagonal, hence invertible, and
   `A = W⁻¹ diag(e) W⁻ᵀ` with `e > 0` is positive definite.

The block form `X0 / 2^s - μ I ≻ 0` used by layer A (`certificate_posDef`) is
`posDef_shift_of_checkPD`.
-/

open Matrix Finset

namespace LayerDProto

/-! ## Lists read as matrices -/

/-- The `k × k` integer matrix read from a list of rows (missing entries are `0`). -/
def toMat (k : ℕ) (L : List (List ℤ)) : Matrix (Fin k) (Fin k) ℤ := fun i j => (L.getD i []).getD j 0

/-- The vector read from a list. -/
def toVec (k : ℕ) (l : List ℤ) : Fin k → ℤ := fun i => l.getD i 0

theorem pow2_eq (b : ℕ) : pow2 b = (2 : ℤ) ^ b := by
  simp [pow2]

theorem dot_eq (xs ys : List ℤ) :
    dot xs ys = ∑ i ∈ range xs.length, xs.getD i 0 * ys.getD i 0 := by
  induction xs generalizing ys with
  | nil => simp [dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [dot]
    | cons y ys =>
      rw [List.length_cons, sum_range_succ', dot, ih ys]
      simp [add_comm]

theorem pk_eq (b : ℕ) (l : List ℤ) :
    pk b l = ∑ i ∈ range l.length, l.getD i 0 * (2 : ℤ) ^ (b * i) := by
  induction l with
  | nil => simp [pk]
  | cons x xs ih =>
    rw [List.length_cons, sum_range_succ', pk, ih, pow2_eq, mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, mul_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.mul_succ, pow_add]
    ring

theorem getD_map_list {α β : Type*} (f : α → β) (L : List α) (d : α) (s : ℕ) :
    (L.map f).getD s (f d) = f (L.getD s d) := by
  induction L generalizing s with
  | nil => simp
  | cons x xs ih => cases s <;> simp [ih]

theorem colPack_spec (k b : ℕ) (rows : List (List ℤ)) (hlen : ∀ r ∈ rows, r.length = k) :
    (colPack k b rows).length = k ∧ ∀ t < k,
      (colPack k b rows).getD t 0 = ∑ j ∈ range rows.length, (rows.getD j []).getD t 0 * 2 ^ (b * j) := by
  induction rows with
  | nil =>
    refine ⟨by simp [colPack], fun t ht => ?_⟩
    simp [colPack, List.getD_eq_getElem?_getD, List.getElem?_replicate, ht]
  | cons r rs ih =>
    have hr : r.length = k := hlen r (by simp)
    obtain ⟨ih1, ih2⟩ := ih fun r' hr' => hlen r' (by simp [hr'])
    refine ⟨by simp [colPack, hr, ih1], fun t ht => ?_⟩
    have ht1 : t < r.length := hr ▸ ht
    have ht2 : t < (colPack k b rs).length := by rw [ih1]; exact ht
    have e1 : (colPack k b (r :: rs)).getD t 0 = r[t] + pow2 b * (colPack k b rs)[t] := by
      simp [colPack, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ht1, ht2]
    have e2 : (colPack k b rs)[t] = (colPack k b rs).getD t 0 := by
      simp [List.getD_eq_getElem?_getD, ht2]
    rw [e1, e2, ih2 t ht, List.length_cons, sum_range_succ', pow2_eq, mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, mul_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      rw [Nat.mul_succ, pow_add]
      ring
    · simp [List.getD_eq_getElem?_getD, ht1]

theorem pdRows_spec (β : ℕ) (V : List ℤ) :
    ∀ (W : List (List ℤ)) (e : List ℤ) (i0 : ℕ), pdRows β V i0 W e = true →
      W.length = e.length ∧
        ∀ i < W.length, dot (W.getD i []) V = e.getD i 0 * pow2 (β * (i0 + i))
  | [], [], _, _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | [], _ :: _, _, h => by simp [pdRows] at h
  | _ :: _, [], _, h => by simp [pdRows] at h
  | w :: W, x :: e, i0, h => by
    simp only [pdRows, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := pdRows_spec β V W e (i0 + 1) h2
    refine ⟨by simp [ih1], fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := ih2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem lowerPos_spec :
    ∀ (W : List (List ℤ)) (i0 : ℕ), lowerPos i0 W = true →
      ∀ i < W.length, (∀ j, i0 + i < j → (W.getD i []).getD j 0 = 0) ∧
        0 < (W.getD i []).getD (i0 + i) 0
  | [], _, _ => fun i hi => absurd hi (by simp)
  | r :: rs, i0, h => by
    simp only [lowerPos, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hz, hp⟩, hrest⟩ := h
    intro i hi
    cases i with
    | zero =>
      refine ⟨fun j hj => ?_, by simpa using hp⟩
      simp only [List.getD_cons_zero, Nat.add_zero] at hj ⊢
      rw [List.getD_eq_getElem?_getD]
      have hdrop : r[j]? = (r.drop (i0 + 1))[j - (i0 + 1)]? := by
        rw [List.getElem?_drop]; congr 1; omega
      rw [hdrop]
      cases hx : (r.drop (i0 + 1))[j - (i0 + 1)]? with
      | none => rfl
      | some x => exact hz x (List.mem_of_getElem? hx)
    | succ i =>
      have := lowerPos_spec rs (i0 + 1) hrest i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem boundedBy_spec (m : ℕ) (l : List ℤ) (h : boundedBy m l = true) (i : ℕ) :
    |l.getD i 0| ≤ m := by
  simp only [boundedBy, List.all_eq_true, decide_eq_true_eq] at h
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => simp
  | some x =>
    have := h x (List.mem_of_getElem? hx)
    simp only [Option.getD_some]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this

/-! ## Balanced digits -/

/-- `2 |∑ⱼ dⱼ Bʲ| ≤ Bⁿ - 1` when every `2 |dⱼ| < B`. -/
theorem digits_bound (B : ℤ) (hB : 1 ≤ B) (d : ℕ → ℤ) :
    ∀ n, (∀ j < n, 2 * |d j| < B) → 2 * |∑ j ∈ range n, d j * B ^ j| ≤ B ^ n - 1
  | 0, _ => by simp
  | n + 1, hd => by
    have ih := digits_bound B hB d n fun j hj => hd j (by omega)
    have hn : 2 * |d n| ≤ B - 1 := by have := hd n (by omega); omega
    rw [sum_range_succ]
    have hpos : 0 ≤ B ^ n := pow_nonneg (by omega) n
    have hadd := abs_add_le (∑ j ∈ range n, d j * B ^ j) (d n * B ^ n)
    rw [abs_mul, abs_of_nonneg hpos] at hadd
    calc 2 * |∑ j ∈ range n, d j * B ^ j + d n * B ^ n|
        ≤ 2 * |∑ j ∈ range n, d j * B ^ j| + 2 * |d n| * B ^ n := by linarith
      _ ≤ (B ^ n - 1) + (B - 1) * B ^ n := by nlinarith
      _ = B ^ (n + 1) - 1 := by ring

/-- A packing with balanced digits (`2 |dⱼ| < B`) vanishes only if every digit vanishes. -/
theorem digits_eq_zero (B : ℤ) (hB : 1 ≤ B) (d : ℕ → ℤ) :
    ∀ n, (∀ j < n, 2 * |d j| < B) → ∑ j ∈ range n, d j * B ^ j = 0 → ∀ j < n, d j = 0
  | 0, _, _ => fun j hj => absurd hj (by omega)
  | n + 1, hd, h => by
    rw [sum_range_succ] at h
    have hlow := digits_bound B hB d n fun j hj => hd j (by omega)
    have hpos : 0 < B ^ n := pow_pos (by omega) n
    have hdn : d n = 0 := by
      by_contra hne
      have h1 : 1 ≤ |d n| := Int.one_le_abs hne
      have h2 : |∑ j ∈ range n, d j * B ^ j| = |d n| * B ^ n := by
        rw [show ∑ j ∈ range n, d j * B ^ j = -(d n * B ^ n) by linarith, abs_neg, abs_mul,
          abs_of_pos hpos]
      nlinarith
    have hrest : ∑ j ∈ range n, d j * B ^ j = 0 := by rw [hdn] at h; simpa using h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact digits_eq_zero B hB d n (fun j hj => hd j (by omega)) hrest j hj
    · exact hdn

/-! ## The checker proves `W A Wᵀ = diag e` -/

theorem sum_fin_eq_range (n : ℕ) (f : ℕ → ℤ) : ∑ i : Fin n, f i = ∑ i ∈ range n, f i :=
  Fin.sum_univ_eq_sum_range f n

theorem waw_eq_diag {k β w a c : ℕ} {A W : List (List ℤ)} {e : List ℤ}
    (h : checkPD k β w a c A W e = true) :
    toMat k W * toMat k A * (toMat k W)ᵀ = diagonal (toVec k e) ∧
      (∀ i : Fin k, 0 < toVec k e i) ∧ (∀ i j : Fin k, i < j → toMat k W i j = 0) ∧
      (∀ i : Fin k, 0 < toMat k W i i) := by
  simp only [checkPD, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAl, hAr⟩, hWl⟩, hWr⟩, hel⟩, hlow⟩, hepos⟩, hAb⟩, hWb⟩, heb⟩, hβ⟩, hrows⟩ := h
  obtain ⟨-, hrow⟩ := pdRows_spec β _ W e 0 hrows
  obtain ⟨hcpl, hcp⟩ := colPack_spec k β W hWr
  have hlow' := lowerPos_spec W 0 hlow
  -- entries of `W`, `A`, `e` are bounded
  have hWb' : ∀ i j, |(W.getD i []).getD j 0| ≤ w := by
    intro i j
    by_cases hi : i < W.length
    · exact boundedBy_spec w _ (hWb _ (by simp [List.getD_eq_getElem?_getD, hi])) j
    · simp [List.getD_eq_getElem?_getD, hi]
  have hAb' : ∀ i j, |(A.getD i []).getD j 0| ≤ a := by
    intro i j
    by_cases hi : i < A.length
    · exact boundedBy_spec a _ (hAb _ (by simp [List.getD_eq_getElem?_getD, hi])) j
    · simp [List.getD_eq_getElem?_getD, hi]
  have heb' : ∀ i, |e.getD i 0| ≤ c := boundedBy_spec c e heb
  have hrowlen : ∀ i < k, (W.getD i []).length = k := fun i hi =>
    hWr _ (by simp [List.getD_eq_getElem?_getD, hWl ▸ hi])
  have hArowlen : ∀ i < k, (A.getD i []).length = k := fun i hi =>
    hAr _ (by simp [List.getD_eq_getElem?_getD, hAl ▸ hi])
  have hB1 : (1 : ℤ) ≤ 2 ^ β := one_le_pow₀ (by norm_num)
  -- notation for the entries
  set Wg : ℕ → ℕ → ℤ := fun i j => (W.getD i []).getD j 0 with hWg
  set Ag : ℕ → ℕ → ℤ := fun i j => (A.getD i []).getD j 0 with hAg
  set M : ℕ → ℕ → ℤ := fun i j => ∑ t ∈ range k, (∑ s ∈ range k, Wg i s * Ag s t) * Wg j t with hM
  have hMent : ∀ i j : Fin k, (toMat k W * toMat k A * (toMat k W)ᵀ) i j = M i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, toMat, hM, hWg, hAg]
    rw [← sum_fin_eq_range]
    refine sum_congr rfl fun t _ => ?_
    rw [← sum_fin_eq_range (f := fun s => (W.getD i []).getD s 0 * (A.getD s []).getD t 0)]
  -- the packed row identity, expanded
  have hV : ∀ s < k, (A.map fun row => dot row (colPack k β W)).getD s 0 =
      ∑ t ∈ range k, Ag s t * ∑ j ∈ range k, Wg j t * ((2 : ℤ) ^ β) ^ j := by
    intro s hs
    rw [show (0 : ℤ) = dot [] (colPack k β W) by simp [dot], getD_map_list, dot_eq, hArowlen s hs]
    refine sum_congr rfl fun t ht => ?_
    rw [hcp t (mem_range.mp ht), hWl]
    simp only [hAg, hWg, pow_mul]
  have hexp : ∀ i < k, ∑ j ∈ range k, M i j * ((2 : ℤ) ^ β) ^ j = e.getD i 0 * ((2 : ℤ) ^ β) ^ i := by
    intro i hi
    have h1 := hrow i (hWl ▸ hi)
    rw [pow2_eq, Nat.zero_add, pow_mul] at h1
    rw [← h1, pdV, dot_eq, hrowlen i hi]
    have hR : ∑ s ∈ range k, (W.getD i []).getD s 0 *
        (A.map fun row => dot row (colPack k β W)).getD s 0 =
        ∑ s ∈ range k, Wg i s * ∑ t ∈ range k, Ag s t * ∑ j ∈ range k, Wg j t * ((2 : ℤ) ^ β) ^ j :=
      sum_congr rfl fun s hs => by rw [hV s (mem_range.mp hs)]
    rw [hR]
    simp only [hM, sum_mul, mul_sum]
    calc ∑ j ∈ range k, ∑ t ∈ range k, ∑ s ∈ range k, Wg i s * Ag s t * Wg j t * ((2 : ℤ) ^ β) ^ j
        = ∑ t ∈ range k, ∑ j ∈ range k, ∑ s ∈ range k, Wg i s * Ag s t * Wg j t * ((2 : ℤ) ^ β) ^ j :=
          sum_comm
      _ = ∑ t ∈ range k, ∑ s ∈ range k, ∑ j ∈ range k, Wg i s * Ag s t * Wg j t * ((2 : ℤ) ^ β) ^ j :=
          sum_congr rfl fun t _ => sum_comm
      _ = ∑ s ∈ range k, ∑ t ∈ range k, ∑ j ∈ range k, Wg i s * Ag s t * Wg j t * ((2 : ℤ) ^ β) ^ j :=
          sum_comm
      _ = _ := by
          refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => sum_congr rfl fun j _ => ?_
          ring
  -- digits are bounded
  have hMb : ∀ i j, |M i j| ≤ (k * k * (w * w * a) : ℕ) := by
    intro i j
    simp only [hM]
    calc |∑ t ∈ range k, (∑ s ∈ range k, Wg i s * Ag s t) * Wg j t|
        ≤ ∑ t ∈ range k, ∑ s ∈ range k, (w * a * w : ℤ) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
          rw [abs_mul]
          refine (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
          rw [sum_mul]
          refine sum_le_sum fun s _ => ?_
          rw [abs_mul]
          have h1 : |Wg i s| ≤ w := hWb' i s
          have h2 : |Ag s t| ≤ a := hAb' s t
          have h3 : |Wg j t| ≤ w := hWb' j t
          have h0' : (0 : ℤ) ≤ |Ag s t| := abs_nonneg _
          have h0'' : (0 : ℤ) ≤ |Wg j t| := abs_nonneg _
          calc |Wg i s| * |Ag s t| * |Wg j t| ≤ w * a * |Wg j t| :=
                mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h0' (by positivity)) h0''
            _ ≤ w * a * w := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (k * k * (w * w * a) : ℕ) := by simp; ring
  have hβ' : (2 * ((k * k * (w * w * a) : ℕ) + (c : ℤ)) : ℤ) < 2 ^ β := by exact_mod_cast hβ
  -- all digits of `W A Wᵀ - diag e` vanish
  have hzero : ∀ i < k, ∀ j < k, M i j = if i = j then e.getD i 0 else 0 := by
    intro i hi
    have hd := digits_eq_zero (2 ^ β) hB1 (fun j => M i j - if i = j then e.getD i 0 else 0) k
      (fun j _ => by
        show 2 * |M i j - (if i = j then e.getD i 0 else 0)| < 2 ^ β
        have h1 := hMb i j
        have h2 := heb' i
        have h3 : |M i j - (if i = j then e.getD i 0 else 0)| ≤ |M i j| + c := by
          split_ifs
          · exact (abs_sub _ _).trans (by linarith)
          · simp only [sub_zero]; linarith [Int.natCast_nonneg c]
        linarith [hβ'])
      (by
        have := hexp i hi
        simp only [sub_mul, sum_sub_distrib, this, ite_mul, zero_mul, sum_ite_eq, mem_range, hi,
          if_true, sub_self])
    intro j hj
    have := hd j hj
    linarith
  refine ⟨?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · ext i j
    rw [hMent, hzero i i.isLt j j.isLt, diagonal_apply]
    simp [Fin.ext_iff, toVec]
  · show 0 < e.getD i 0
    have hi : (i : ℕ) < e.length := by rw [hel]; exact i.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hepos _ (List.getElem_mem hi)
  · have hi : (i : ℕ) < W.length := by rw [hWl]; exact i.isLt
    exact (hlow' i hi).1 j (by simpa using hij)
  · have hi : (i : ℕ) < W.length := by rw [hWl]; exact i.isLt
    simpa using (hlow' i hi).2

/-- **Soundness of `checkPD`.** -/
theorem posDef_of_checkPD {k β w a c : ℕ} {A W : List (List ℤ)} {e : List ℤ}
    (h : checkPD k β w a c A W e = true) :
    ((toMat k A).map (Int.cast : ℤ → ℝ)).PosDef := by
  obtain ⟨hE, he, hl, hd⟩ := waw_eq_diag h
  set Wr := (toMat k W).map (Int.cast : ℤ → ℝ) with hWr
  set Ar := (toMat k A).map (Int.cast : ℤ → ℝ) with hAr
  have hE' : Wr * Ar * Wrᵀ = diagonal fun i => (toVec k e i : ℝ) := by
    have := congrArg (fun M => M.map (Int.castRingHom ℝ)) hE
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [diagonal_map (by simp)] at this
    simpa [hWr, hAr] using this
  have htri : Wr.BlockTriangular OrderDual.toDual := fun i j hij => by
    simp [hWr, hl i j (by simpa using hij)]
  have hdet : IsUnit Wr.det := by
    rw [det_of_lowerTriangular Wr htri, isUnit_iff_ne_zero]
    exact prod_ne_zero_iff.mpr fun i _ => by simp [hWr]; exact (hd i).ne'
  have hdetT : IsUnit Wrᵀ.det := by rwa [det_transpose]
  have hD : (diagonal fun i => (toVec k e i : ℝ)).PosDef :=
    posDef_diagonal_iff.mpr fun i => by exact_mod_cast he i
  have hA : Ar = Wr⁻¹ * (Wr * Ar * Wrᵀ) * (Wr⁻¹)ᴴ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_nonsing_inv]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hdetT, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
  rw [hA, hE']
  refine hD.mul_mul_conjTranspose_same ?_
  exact vecMul_injective_iff_isUnit.mpr ((isUnit_nonsing_inv_iff).mpr ((isUnit_iff_isUnit_det _).mpr hdet))

/-! ## The diagonally dominant (short `W`) variant -/

/-- A real symmetric matrix with `∑ⱼ |Eᵢⱼ| < 2 Eᵢᵢ` for every row is positive definite. -/
theorem pow_pos_of_ne_zero_of_two {y : ℝ} (h : y ≠ 0) : 0 < y ^ 2 := by positivity

theorem posDef_of_diagDom {k : ℕ} (E : Matrix (Fin k) (Fin k) ℝ) (hs : Eᵀ = E)
    (hd : ∀ i, ∑ j, |E i j| < 2 * E i i) : E.PosDef := by
  have hherm : E.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hs]
  refine ⟨hherm, fun x hx => ?_⟩
  have hdiag : ∀ i, 0 < E i i := fun i => by
    have h1 : |E i i| ≤ ∑ j, |E i j| :=
      single_le_sum (f := fun j => |E i j|) (fun j _ => abs_nonneg _) (mem_univ i)
    have := hd i
    have := le_abs_self (E i i)
    linarith
  have hterm : ∀ i j, (if i = j then 2 * E i i * x i ^ 2 else 0) - |E i j| * (x i ^ 2 + x j ^ 2) / 2 ≤
      x i * (E i j * x j) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, abs_of_pos (hdiag i)]
      nlinarith
    · rw [if_neg h]
      rcases abs_cases (E i j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
      · nlinarith [mul_nonneg h2 (sq_nonneg (x i + x j))]
      · nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr h2)) (sq_nonneg (x i - x j))]
  have hq : star x ⬝ᵥ (E *ᵥ x) = ∑ i, ∑ j, x i * (E i j * x j) := by
    simp [dotProduct, mulVec, star_trivial, mul_sum]
  have hsym : ∀ i j, |E i j| = |E j i| := fun i j => by
    have h := congrFun (congrFun hs i) j
    simp only [transpose_apply] at h
    rw [h]
  have e1 : ∑ i, ∑ j, |E i j| * x j ^ 2 = ∑ i, ∑ j, |E i j| * x i ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hsym]
  have hlow : ∑ i, ∑ j, ((if i = j then 2 * E i i * x i ^ 2 else 0) - |E i j| * (x i ^ 2 + x j ^ 2) / 2)
      = ∑ i, (2 * E i i - ∑ j, |E i j|) * x i ^ 2 := by
    have hsplit : ∀ i j, (if i = j then 2 * E i i * x i ^ 2 else 0) - |E i j| * (x i ^ 2 + x j ^ 2) / 2 =
        (if i = j then 2 * E i i * x i ^ 2 else 0) - |E i j| * x i ^ 2 / 2 - |E i j| * x j ^ 2 / 2 :=
      fun i j => by ring
    simp only [hsplit, sum_sub_distrib, sum_ite_eq, mem_univ, if_true, ← sum_div]
    rw [e1]
    simp only [sub_mul, sum_mul, sum_sub_distrib]
    ring
  rw [hq]
  have hge : ∑ i, (2 * E i i - ∑ j, |E i j|) * x i ^ 2 ≤ ∑ i, ∑ j, x i * (E i j * x j) := by
    rw [← hlow]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx
  have hpos : 0 < ∑ i, (2 * E i i - ∑ j, |E i j|) * x i ^ 2 := by
    refine sum_pos' (fun i _ => mul_nonneg (by linarith [hd i]) (sq_nonneg _)) ⟨i0, mem_univ _, ?_⟩
    exact mul_pos (by linarith [hd i0]) (pow_pos_of_ne_zero_of_two hi0)
  linarith

/-- Entry `(i, j)` of `W A Wᵀ` for list matrices. -/
def wawEnt (k : ℕ) (A W : List (List ℤ)) (i j : ℕ) : ℤ :=
  ∑ t ∈ range k, (∑ s ∈ range k, (W.getD i []).getD s 0 * (A.getD s []).getD t 0) * (W.getD j []).getD t 0

theorem toMat_waw (k : ℕ) (A W : List (List ℤ)) (i j : Fin k) :
    (toMat k W * toMat k A * (toMat k W)ᵀ) i j = wawEnt k A W i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, toMat, wawEnt]
  rw [← sum_fin_eq_range]
  refine sum_congr rfl fun t _ => ?_
  rw [← sum_fin_eq_range (f := fun s => (W.getD i []).getD s 0 * (A.getD s []).getD t 0)]

theorem pdV_row {k β : ℕ} {A W : List (List ℤ)} (hAl : A.length = k) (hAr : ∀ r ∈ A, r.length = k)
    (hWl : W.length = k) (hWr : ∀ r ∈ W, r.length = k) (i : ℕ) (hi : i < k) :
    dot (W.getD i []) (pdV k β A W) = ∑ j ∈ range k, wawEnt k A W i j * ((2 : ℤ) ^ β) ^ j := by
  obtain ⟨-, hcp⟩ := colPack_spec k β W hWr
  have hrowlen : ∀ i < k, (W.getD i []).length = k := fun i hi =>
    hWr _ (by simp [List.getD_eq_getElem?_getD, hWl ▸ hi])
  have hArowlen : ∀ i < k, (A.getD i []).length = k := fun i hi =>
    hAr _ (by simp [List.getD_eq_getElem?_getD, hAl ▸ hi])
  set Wg : ℕ → ℕ → ℤ := fun i j => (W.getD i []).getD j 0 with hWg
  set Ag : ℕ → ℕ → ℤ := fun i j => (A.getD i []).getD j 0 with hAg
  have hV : ∀ s < k, (A.map fun row => dot row (colPack k β W)).getD s 0 =
      ∑ t ∈ range k, Ag s t * ∑ j ∈ range k, Wg j t * ((2 : ℤ) ^ β) ^ j := by
    intro s hs
    rw [show (0 : ℤ) = dot [] (colPack k β W) by simp [dot], getD_map_list, dot_eq, hArowlen s hs]
    refine sum_congr rfl fun t ht => ?_
    rw [hcp t (mem_range.mp ht), hWl]
    simp only [hAg, hWg, pow_mul]
  rw [pdV, dot_eq, hrowlen i hi]
  have hR : ∑ s ∈ range k, (W.getD i []).getD s 0 *
      (A.map fun row => dot row (colPack k β W)).getD s 0 =
      ∑ s ∈ range k, Wg i s * ∑ t ∈ range k, Ag s t * ∑ j ∈ range k, Wg j t * ((2 : ℤ) ^ β) ^ j :=
    sum_congr rfl fun s hs => by rw [hV s (mem_range.mp hs)]
  rw [hR]
  simp only [wawEnt, sum_mul, mul_sum]
  calc ∑ s ∈ range k, ∑ t ∈ range k, ∑ j ∈ range k, Wg i s * (Ag s t * (Wg j t * ((2 : ℤ) ^ β) ^ j))
      = ∑ t ∈ range k, ∑ s ∈ range k, ∑ j ∈ range k, Wg i s * (Ag s t * (Wg j t * ((2 : ℤ) ^ β) ^ j)) :=
        sum_comm
    _ = ∑ t ∈ range k, ∑ j ∈ range k, ∑ s ∈ range k, Wg i s * (Ag s t * (Wg j t * ((2 : ℤ) ^ β) ^ j)) :=
        sum_congr rfl fun t _ => sum_comm
    _ = ∑ j ∈ range k, ∑ t ∈ range k, ∑ s ∈ range k, Wg i s * (Ag s t * (Wg j t * ((2 : ℤ) ^ β) ^ j)) :=
        sum_comm
    _ = _ := by
        refine sum_congr rfl fun j _ => sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
        simp only [hWg, hAg]
        ring

theorem wawEnt_bound {k w a : ℕ} {A W : List (List ℤ)} (hWb : ∀ i j, |(W.getD i []).getD j 0| ≤ w)
    (hAb : ∀ i j, |(A.getD i []).getD j 0| ≤ a) (i j : ℕ) :
    |wawEnt k A W i j| ≤ (k * k * (w * w * a) : ℕ) := by
  unfold wawEnt
  calc |∑ t ∈ range k, (∑ s ∈ range k, (W.getD i []).getD s 0 * (A.getD s []).getD t 0) *
          (W.getD j []).getD t 0|
      ≤ ∑ t ∈ range k, ∑ s ∈ range k, (w * a * w : ℤ) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
        rw [abs_mul]
        refine (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
        rw [sum_mul]
        refine sum_le_sum fun s _ => ?_
        rw [abs_mul]
        have h1 := hWb i s
        have h2 := hAb s t
        have h3 := hWb j t
        have h0' : (0 : ℤ) ≤ |(A.getD s []).getD t 0| := abs_nonneg _
        have h0'' : (0 : ℤ) ≤ |(W.getD j []).getD t 0| := abs_nonneg _
        calc |(W.getD i []).getD s 0| * |(A.getD s []).getD t 0| * |(W.getD j []).getD t 0|
            ≤ w * a * |(W.getD j []).getD t 0| :=
              mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h0' (by positivity)) h0''
          _ ≤ w * a * w := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (k * k * (w * w * a) : ℕ) := by simp; ring

/-- Congruence by a lower-triangular `W` with positive diagonal reflects positive definiteness. -/
theorem posDef_of_congr {k : ℕ} {Wz Az : Matrix (Fin k) (Fin k) ℤ}
    (hl : ∀ i j : Fin k, i < j → Wz i j = 0) (hd : ∀ i, 0 < Wz i i)
    (hE : ((Wz * Az * Wzᵀ).map (Int.cast : ℤ → ℝ)).PosDef) : (Az.map (Int.cast : ℤ → ℝ)).PosDef := by
  set Wr := Wz.map (Int.cast : ℤ → ℝ) with hWr
  set Ar := Az.map (Int.cast : ℤ → ℝ) with hAr
  have hE' : (Wz * Az * Wzᵀ).map (Int.cast : ℤ → ℝ) = Wr * Ar * Wrᵀ := by
    have := (Matrix.map_mul (L := Wz * Az) (M := Wzᵀ) (f := Int.castRingHom ℝ))
    rw [Matrix.map_mul (L := Wz) (M := Az)] at this
    simpa [hWr, hAr, Matrix.transpose_map] using this
  have htri : Wr.BlockTriangular OrderDual.toDual := fun i j hij => by
    simp [hWr, hl i j (by simpa using hij)]
  have hdet : IsUnit Wr.det := by
    rw [det_of_lowerTriangular Wr htri, isUnit_iff_ne_zero]
    exact prod_ne_zero_iff.mpr fun i _ => by simp [hWr]; exact (hd i).ne'
  have hdetT : IsUnit Wrᵀ.det := by rwa [det_transpose]
  have hA : Ar = Wr⁻¹ * (Wr * Ar * Wrᵀ) * (Wr⁻¹)ᴴ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_nonsing_inv]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hdetT, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
  rw [hA]
  rw [hE'] at hE
  refine hE.mul_mul_conjTranspose_same ?_
  exact vecMul_injective_iff_isUnit.mpr ((isUnit_nonsing_inv_iff).mpr ((isUnit_iff_isUnit_det _).mpr hdet))

theorem unpkN_length (b : ℕ) : ∀ (n q : ℕ), (unpkN b n q).length = n
  | 0, _ => rfl
  | n + 1, q => by simp [unpkN, unpkN_length b n]

theorem unpk_length (b n : ℕ) (P : ℤ) : (unpk b n P).length = n := by
  simp [unpk, unpkN_length]

theorem sumAbs_eq (l : List ℤ) : (sumAbs l : ℤ) = ∑ j ∈ range l.length, |l.getD j 0| := by
  induction l with
  | nil => simp [sumAbs]
  | cons x xs ih =>
    rw [List.length_cons, sum_range_succ', sumAbs]
    push_cast
    rw [ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Int.abs_eq_natAbs]
    ring

theorem ddRows_spec (β k ed : ℕ) (V : List ℤ) :
    ∀ (W : List (List ℤ)) (i0 : ℕ), ddRows β k ed V i0 W = true →
      ∀ i < W.length, pk β (unpk β k (dot (W.getD i []) V)) = dot (W.getD i []) V ∧
        boundedBy ed (unpk β k (dot (W.getD i []) V)) = true ∧
        (sumAbs (unpk β k (dot (W.getD i []) V)) : ℤ) <
          2 * (unpk β k (dot (W.getD i []) V)).getD (i0 + i) 0
  | [], _, _ => fun i hi => absurd hi (by simp)
  | w :: W, i0, h => by
    simp only [ddRows, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    intro i hi
    cases i with
    | zero => exact ⟨h1, h2, by simpa using h3⟩
    | succ i =>
      have := ddRows_spec β k ed V W (i0 + 1) h4 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem transp_spec (k : ℕ) : ∀ (L : List (List ℤ)), (∀ r ∈ L, r.length = k) →
    (transp k L).length = k ∧ ∀ j < k, ∀ i, ((transp k L).getD j []).getD i 0 = (L.getD i []).getD j 0
  | [], _ => ⟨by simp [transp], fun j hj i => by
      simp [transp, List.getD_eq_getElem?_getD, List.getElem?_replicate, hj]⟩
  | r :: rs, hlen => by
    have hr : r.length = k := hlen r (by simp)
    obtain ⟨ih1, ih2⟩ := transp_spec k rs fun r' hr' => hlen r' (by simp [hr'])
    refine ⟨by simp [transp, hr, ih1], fun j hj i => ?_⟩
    have hj1 : j < r.length := hr ▸ hj
    have hj2 : j < (transp k rs).length := by rw [ih1]; exact hj
    have e1 : (transp k (r :: rs)).getD j [] = r[j] :: (transp k rs)[j] := by
      simp [transp, List.getD_eq_getElem?_getD, hj1, hj2]
    have e2 : (transp k rs)[j] = (transp k rs).getD j [] := by
      simp [List.getD_eq_getElem?_getD, hj2]
    rw [e1]
    cases i with
    | zero => simp [List.getD_eq_getElem?_getD, hj1]
    | succ i => rw [List.getD_cons_succ, e2, ih2 j hj i, List.getD_cons_succ]

/-- **Soundness of `checkPDdd`** (short `W`, diagonally dominant `W A Wᵀ`). -/
theorem posDef_of_checkPDdd {k β w a ed : ℕ} {A W : List (List ℤ)}
    (h : checkPDdd k β w a ed A W = true) : ((toMat k A).map (Int.cast : ℤ → ℝ)).PosDef := by
  simp only [checkPDdd, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hAl, hAr⟩, hsym⟩, hWl⟩, hWr⟩, hlow⟩, hAb⟩, hWb⟩, hβ⟩, hrows⟩ := h
  have hlow' := lowerPos_spec W 0 hlow
  have hWb' : ∀ i j, |(W.getD i []).getD j 0| ≤ w := by
    intro i j
    by_cases hi : i < W.length
    · exact boundedBy_spec w _ (hWb _ (by simp [List.getD_eq_getElem?_getD, hi])) j
    · simp [List.getD_eq_getElem?_getD, hi]
  have hAb' : ∀ i j, |(A.getD i []).getD j 0| ≤ a := by
    intro i j
    by_cases hi : i < A.length
    · exact boundedBy_spec a _ (hAb _ (by simp [List.getD_eq_getElem?_getD, hi])) j
    · simp [List.getD_eq_getElem?_getD, hi]
  have hB1 : (1 : ℤ) ≤ 2 ^ β := one_le_pow₀ (by norm_num)
  have hβ' : (2 * ((k * k * (w * w * a) : ℕ) + (ed : ℤ)) : ℤ) < 2 ^ β := by exact_mod_cast hβ
  have hrow := ddRows_spec β k ed _ W 0 hrows
  -- the unpacked rows are the rows of `W A Wᵀ`
  have hent : ∀ i < k, ∀ j < k,
      (unpk β k (dot (W.getD i []) (pdV k β A W))).getD j 0 = wawEnt k A W i j := by
    intro i hi
    obtain ⟨hpk, hbd, -⟩ := hrow i (by rw [hWl]; exact hi)
    set E := unpk β k (dot (W.getD i []) (pdV k β A W)) with hE
    have hEl : E.length = k := unpk_length β k _
    have hpk' := hpk
    rw [pk_eq, hEl, pdV_row hAl hAr hWl hWr i hi] at hpk'
    simp only [pow_mul] at hpk'
    have hd := digits_eq_zero (2 ^ β) hB1 (fun j => wawEnt k A W i j - E.getD j 0) k
      (fun j _ => by
        show 2 * |wawEnt k A W i j - E.getD j 0| < 2 ^ β
        have h1 := wawEnt_bound (k := k) hWb' hAb' i j
        have h2 := boundedBy_spec ed E hbd j
        have h3 := abs_sub (wawEnt k A W i j) (E.getD j 0)
        linarith)
      (by simp only [sub_mul, sum_sub_distrib, hpk', sub_self])
    intro j hj
    have := hd j hj
    linarith
  -- `W A Wᵀ` is symmetric and diagonally dominant
  obtain ⟨-, htr⟩ := transp_spec k A hAr
  have hAsym : (toMat k A)ᵀ = toMat k A := by
    ext i j
    simp only [transpose_apply, toMat]
    rw [← htr i i.isLt j, hsym]
  refine posDef_of_congr (Wz := toMat k W) (fun i j hij => ?_) (fun i => ?_) ?_
  · have hi : (i : ℕ) < W.length := by rw [hWl]; exact i.isLt
    exact (hlow' i hi).1 j (by simpa using hij)
  · have hi : (i : ℕ) < W.length := by rw [hWl]; exact i.isLt
    simpa using (hlow' i hi).2
  · refine posDef_of_diagDom _ ?_ fun i => ?_
    · rw [← Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        hAsym, Matrix.mul_assoc]
    · have hi : (i : ℕ) < W.length := by rw [hWl]; exact i.isLt
      obtain ⟨-, -, hdd⟩ := hrow i hi
      rw [sumAbs_eq, unpk_length, Nat.zero_add, hent i i.isLt i i.isLt] at hdd
      simp only [Matrix.map_apply, toMat_waw]
      have hs : ∑ j : Fin k, |((wawEnt k A W i j : ℤ) : ℝ)| = ((∑ j ∈ range k, |wawEnt k A W i j| : ℤ) : ℝ) := by
        push_cast
        rw [← Fin.sum_univ_eq_sum_range (fun j => |(wawEnt k A W i j : ℝ)|) k]
      rw [hs]
      have : ∑ j ∈ range k, |(unpk β k (dot (W.getD i []) (pdV k β A W))).getD j 0| =
          ∑ j ∈ range k, |wawEnt k A W i j| :=
        sum_congr rfl fun j hj => by rw [hent i i.isLt j (mem_range.mp hj)]
      rw [this] at hdd
      exact_mod_cast hdd

/-! ## The block form used by layer A -/

theorem shiftDiag_getD (sh : ℤ) :
    ∀ (L : List (List ℤ)) (i0 i j : ℕ), i < L.length → j < (L.getD i []).length →
      ((shiftDiag sh i0 L).getD i []).getD j 0 =
        (L.getD i []).getD j 0 - if j = i0 + i then sh else 0
  | [], _, _, _, hi, _ => absurd hi (by simp)
  | r :: rs, i0, i, j, hi, hj => by
    cases i with
    | zero =>
      simp only [shiftDiag, List.getD_cons_zero, Nat.add_zero] at hj ⊢
      by_cases hji : j = i0
      · subst hji
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hj, List.getElem?_eq_getElem hj]
      · have hne : i0 ≠ j := fun h => hji h.symm
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, hji]
    | succ i =>
      simp only [shiftDiag, List.getD_cons_succ] at hj ⊢
      rw [shiftDiag_getD sh rs (i0 + 1) i j (by simpa using hi) hj,
        show i0 + 1 + i = i0 + (i + 1) by omega]

/-- **Block form** (generic): from positive definiteness of `X0 - sh I` (as a list matrix with
`sh = mn · 2^(s - me)`) to `X0 / 2^s - (mn / 2^me) I ≻ 0`, the hypothesis `hPD` of layer A's
`WernerEndpoint.certificate_posDef` (with `μ = mn / 2^me`). -/
theorem posDef_shift_of_posDef {k : ℕ} {X0 : List (List ℤ)} (s mn me : ℕ) (hme : me ≤ s)
    (hAl : (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0).length = k)
    (hAr : ∀ r ∈ shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0, r.length = k)
    (hA : ((toMat k (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0)).map (Int.cast : ℤ → ℝ)).PosDef) :
    (((2 : ℝ) ^ (s : ℤ))⁻¹ • (toMat k X0).map (Int.cast : ℤ → ℝ) -
      ((mn : ℝ) / 2 ^ me) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  have hlen : ∀ (L : List (List ℤ)) (i0 : ℕ), (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) i0 L).length = L.length := by
    intro L; induction L with
    | nil => intro; rfl
    | cons r rs ih => intro i0; simp [shiftDiag, ih]
  have hrowlen : ∀ (L : List (List ℤ)) (i0 i : ℕ),
      ((shiftDiag ((mn : ℤ) * 2 ^ (s - me)) i0 L).getD i []).length = (L.getD i []).length := by
    intro L; induction L with
    | nil => intro i0 i; simp [shiftDiag]
    | cons r rs ih =>
      intro i0 i
      cases i with
      | zero => simp [shiftDiag]
      | succ i => simp only [shiftDiag, List.getD_cons_succ]; exact ih (i0 + 1) i
  have hXl : X0.length = k := by rw [← hAl, hlen]
  have hXr : ∀ i < k, (X0.getD i []).length = k := by
    intro i hi
    rw [← hrowlen X0 0 i]
    apply hAr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hAl]; exact hi)]
    exact List.getElem_mem _
  have hent : (toMat k (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0)).map (Int.cast : ℤ → ℝ) =
      (toMat k X0).map (Int.cast : ℤ → ℝ) - (((mn : ℤ) * 2 ^ (s - me) : ℤ) : ℝ) • 1 := by
    ext i j
    simp only [Matrix.map_apply, toMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [shiftDiag_getD _ X0 0 i j (by rw [hXl]; exact i.isLt) (by rw [hXr i i.isLt]; exact j.isLt),
      Nat.zero_add]
    by_cases hij : (j : ℕ) = i
    · have : i = j := Fin.ext hij.symm
      simp [hij, this]
    · have : i ≠ j := fun h => hij (by rw [h])
      simp [hij, this]
  rw [hent] at hA
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (s : ℤ))⁻¹ := by positivity
  have hsm := hA.smul hpos
  convert hsm using 1
  rw [smul_sub, smul_smul]
  congr 1
  congr 1
  push_cast
  rw [zpow_natCast]
  have h2 : (2 : ℝ) ^ s = 2 ^ (s - me) * 2 ^ me := by rw [← pow_add, Nat.sub_add_cancel hme]
  rw [h2]
  field_simp

/-- **Block form for `checkPD`.** -/
theorem posDef_shift_of_checkPD {k β w a c : ℕ} {X0 W : List (List ℤ)} {e : List ℤ}
    (s mn me : ℕ) (hme : me ≤ s)
    (h : checkPD k β w a c (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0) W e = true) :
    (((2 : ℝ) ^ (s : ℤ))⁻¹ • (toMat k X0).map (Int.cast : ℤ → ℝ) -
      ((mn : ℝ) / 2 ^ me) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  have hA := posDef_of_checkPD h
  simp only [checkPD, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAl, hAr⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact posDef_shift_of_posDef s mn me hme hAl hAr hA

/-- **Block form for `checkPDdd`.** -/
theorem posDef_shift_of_checkPDdd {k β w a ed : ℕ} {X0 W : List (List ℤ)}
    (s mn me : ℕ) (hme : me ≤ s)
    (h : checkPDdd k β w a ed (shiftDiag ((mn : ℤ) * 2 ^ (s - me)) 0 X0) W = true) :
    (((2 : ℝ) ^ (s : ℤ))⁻¹ • (toMat k X0).map (Int.cast : ℤ → ℝ) -
      ((mn : ℝ) / 2 ^ me) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  have hA := posDef_of_checkPDdd h
  simp only [checkPDdd, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hAl, hAr⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact posDef_shift_of_posDef s mn me hme hAl hAr hA

end LayerDProto

#print axioms LayerDProto.posDef_of_checkPD
#print axioms LayerDProto.posDef_shift_of_checkPD
#print axioms LayerDProto.posDef_shift_of_checkPDdd
