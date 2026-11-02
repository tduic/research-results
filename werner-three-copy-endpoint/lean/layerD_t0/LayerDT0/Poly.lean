import WernerEndpoint.AllD_Poly
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Layer D (t = 0): integer polynomials as coefficient lists, checked by evaluation at `2^β`

* `toP l = ∑ lᵢ Xⁱ ∈ ℤ[X]` (low coefficient first), `horner x l` its value at an integer (kernel
  computable), `ev x l` its value at a real.
* `CB p M D`: every coefficient of `p` is at most `M` in absolute value and the coefficients of
  index `≥ D` vanish; closed under `+`, `-`, `*`, `Xˡ ·` and finite sums (`CB_add`, `CB_mul`, …).
* **Kronecker substitution** (`eq_zero_of_eval_eq_zero`): an integer polynomial whose coefficients
  are bounded by `M` and which vanishes at one integer `x > 2M` is zero. So a polynomial identity
  between list-expressions is checked by one big-integer evaluation plus an a priori coefficient bound.
* `domPos`: leading-term dominance `∑_{i<n} |lᵢ| 4ⁱ < lₙ 4ⁿ` gives `ev x l > 0` for every real `x ≥ 4`.
* `ev_rev`: `xⁿ · ev (1/x) l = ev x (rev n l)` (the verifier's Laurent identities at `t = 1/d`).
-/

open Polynomial Finset

namespace LayerDT0

/-! ### Lists as polynomials -/

noncomputable def toP : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * toP l

def horner (x : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + x * horner x l

theorem eval_toP (x : ℤ) : ∀ l, (toP l).eval x = horner x l
  | [] => by simp [toP, horner]
  | a :: l => by simp [toP, horner, eval_toP x l]

theorem coeff_toP : ∀ (l : List ℤ) (i : ℕ), (toP l).coeff i = l.getD i 0
  | [], i => by simp [toP]
  | a :: l, 0 => by simp [toP]
  | a :: l, i + 1 => by
    show (C a + X * toP l).coeff (i + 1) = _
    rw [coeff_add, coeff_C, coeff_X_mul, coeff_toP l i]; simp

/-- Value at a real point. -/
noncomputable def ev (x : ℝ) (l : List ℤ) : ℝ := (toP l).eval₂ (Int.castRingHom ℝ) x

theorem ev_cons (x : ℝ) (a : ℤ) (l : List ℤ) : ev x (a :: l) = a + x * ev x l := by
  simp only [ev, toP, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  rfl

theorem ev_nil (x : ℝ) : ev x [] = 0 := by simp [ev, toP]

theorem ev_eq_sum (x : ℝ) : ∀ (l : List ℤ) (N : ℕ), l.length ≤ N →
    ev x l = ∑ i ∈ range N, (l.getD i 0 : ℝ) * x ^ i
  | [], N, _ => by simp [ev_nil]
  | a :: l, 0, h => by simp at h
  | a :: l, N + 1, h => by
    rw [ev_cons, ev_eq_sum x l N (by simpa using h), sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => by ring

theorem lsum_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ k, ((List.range k).map f).sum = ∑ i ∈ range k, f i
  | 0 => by simp
  | k + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsum_eq f k, sum_range_succ]; simp

/-! ### Coefficient bounds -/

def CB (p : ℤ[X]) (M : ℤ) (D : ℕ) : Prop := (∀ i, |p.coeff i| ≤ M) ∧ ∀ i, D ≤ i → p.coeff i = 0

theorem CB.nonneg {p : ℤ[X]} {M : ℤ} {D : ℕ} (h : CB p M D) : 0 ≤ M := (abs_nonneg _).trans (h.1 0)

theorem CB.mono {p : ℤ[X]} {M M' : ℤ} {D D' : ℕ} (h : CB p M D) (hM : M ≤ M') (hD : D ≤ D') :
    CB p M' D' := ⟨fun i => (h.1 i).trans hM, fun i hi => h.2 i (hD.trans hi)⟩

theorem CB_toP {l : List ℤ} {M : ℤ} {D : ℕ} (hM : 0 ≤ M) (hb : ∀ a ∈ l, |a| ≤ M) (hl : l.length ≤ D) :
    CB (toP l) M D := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · rw [coeff_toP, List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => simpa using hM
    | some a => exact hb a (List.mem_of_getElem? h)
  · rw [coeff_toP, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem CB_add {p q : ℤ[X]} {M M' : ℤ} {D D' : ℕ} (hp : CB p M D) (hq : CB q M' D') :
    CB (p + q) (M + M') (max D D') :=
  ⟨fun i => by rw [coeff_add]; exact (abs_add_le _ _).trans (add_le_add (hp.1 i) (hq.1 i)),
    fun i hi => by rw [coeff_add, hp.2 i (le_of_max_le_left hi), hq.2 i (le_of_max_le_right hi),
      add_zero]⟩

theorem CB_sub {p q : ℤ[X]} {M M' : ℤ} {D D' : ℕ} (hp : CB p M D) (hq : CB q M' D') :
    CB (p - q) (M + M') (max D D') :=
  ⟨fun i => by rw [coeff_sub]; exact (abs_sub _ _).trans (add_le_add (hp.1 i) (hq.1 i)),
    fun i hi => by rw [coeff_sub, hp.2 i (le_of_max_le_left hi), hq.2 i (le_of_max_le_right hi),
      sub_zero]⟩

theorem CB_X_pow_mul {p : ℤ[X]} {M : ℤ} {D : ℕ} (hp : CB p M D) (l : ℕ) : CB (X ^ l * p) M (D + l) := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · rw [coeff_X_pow_mul']; split_ifs
    · exact hp.1 _
    · simpa using hp.nonneg
  · rw [coeff_X_pow_mul']; split_ifs
    · exact hp.2 _ (by omega)
    · rfl

theorem CB_sum {ι : Type*} (s : Finset ι) {f : ι → ℤ[X]} {M : ℤ} {D : ℕ} (hM : 0 ≤ M)
    (h : ∀ i ∈ s, CB (f i) M D) : CB (∑ i ∈ s, f i) (s.card * M) D := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨fun i => by simp, fun i _ => by simp⟩
  | cons a s ha ih =>
    rw [sum_cons, card_cons]
    have := CB_add (h a (mem_cons_self a s)) (ih fun i hi => h i (mem_cons_of_mem hi))
    refine this.mono (by push_cast; linarith) (by simp)

theorem CB_mul {p q : ℤ[X]} {M M' : ℤ} {D D' : ℕ} (hp : CB p M D) (hq : CB q M' D') :
    CB (p * q) (D * (M * M')) (D + D') := by
  have hM := hp.nonneg
  have hM' := hq.nonneg
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [coeff_mul]
    calc |∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2|
        ≤ ∑ x ∈ antidiagonal n, |p.coeff x.1 * q.coeff x.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ antidiagonal n, if x.1 < D then M * M' else 0 := by
          refine sum_le_sum fun x _ => ?_
          rw [abs_mul]
          split_ifs with h
          · exact mul_le_mul (hp.1 _) (hq.1 _) (abs_nonneg _) hM
          · rw [hp.2 _ (not_lt.mp h)]; simp
      _ = ((antidiagonal n).filter fun x => x.1 < D).card * (M * M') := by
          rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      _ ≤ D * (M * M') := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hM hM')
          have : ((antidiagonal n).filter fun x => x.1 < D).card ≤ (range D).card := by
            refine card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
            · simp only [coe_filter, Set.mem_setOf_eq] at hx; simpa using hx.2
            · simp only [coe_filter, mem_antidiagonal, Set.mem_setOf_eq] at hx hy
              exact Prod.ext hxy (by simp at hxy; omega)
          simpa using this
  · rw [coeff_mul]
    refine sum_eq_zero fun x hx => ?_
    rw [mem_antidiagonal] at hx
    by_cases h : D ≤ x.1
    · rw [hp.2 _ h, zero_mul]
    · rw [hq.2 _ (by omega), mul_zero]

/-! ### Kronecker substitution -/

theorem eq_zero_of_eval_eq_zero (M x : ℤ) (hx : 2 * M < x) :
    ∀ (n : ℕ) (P : ℤ[X]), P.natDegree = n → (∀ i, |P.coeff i| ≤ M) → P.eval x = 0 → P = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hb h
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hx0 : 0 < x := by linarith
  have key := X_mul_divX_add P
  have he : x * (divX P).eval x + P.coeff 0 = 0 := by
    have := congrArg (eval x) key
    simp only [eval_add, eval_mul, eval_X, eval_C] at this
    rw [this, h]
  have hc : P.coeff 0 = 0 := by
    by_contra hc
    have h1 : P.coeff 0 = -(x * (divX P).eval x) := by linarith
    have h2 : (divX P).eval x ≠ 0 := by intro h0; apply hc; rw [h1, h0]; simp
    have h3 : x ≤ |P.coeff 0| := by
      rw [h1, abs_neg, abs_mul, abs_of_pos hx0]
      exact le_mul_of_one_le_right hx0.le (Int.one_le_abs h2)
    have := hb 0
    linarith
  have he' : (divX P).eval x = 0 := by
    rw [hc, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hx0.ne'
  by_cases h0 : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h0, hc, C_0]
  · have hd : (divX P).natDegree < n := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hz := ih _ hd (divX P) rfl (fun i => by rw [coeff_divX]; exact hb _) he'
    rw [← key, hz, hc]; simp

theorem eq_zero_of_CB_eval {P : ℤ[X]} {M : ℤ} {D : ℕ} (hP : CB P M D) {x : ℤ} (hx : 2 * M < x)
    (h : P.eval x = 0) : P = 0 :=
  eq_zero_of_eval_eq_zero M x hx _ P rfl hP.1 h

/-! ### Bound checks on data -/

def bndL (M : ℤ) (D : ℕ) (l : List ℤ) : Bool := decide (l.length ≤ D) && l.all fun a => decide (|a| ≤ M)

theorem CB_of_bndL {M : ℤ} {D : ℕ} {l : List ℤ} (hM : 0 ≤ M) (h : bndL M D l = true) : CB (toP l) M D := by
  simp only [bndL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact CB_toP hM h.2 h.1

/-! ### Positivity for `x ≥ 4` by leading-term dominance -/

def domPos (l : List ℤ) : Bool :=
  decide (0 < l.getD (l.length - 1) 0) &&
    decide (((List.range (l.length - 1)).map fun i => |l.getD i 0| * 4 ^ i).sum <
      l.getD (l.length - 1) 0 * 4 ^ (l.length - 1))

theorem domPos_spec {l : List ℤ} (h : domPos l = true) {x : ℝ} (hx : 4 ≤ x) : 0 < ev x l := by
  simp only [domPos, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlead, hdom⟩ := h
  set n := l.length - 1
  have hlen : l.length = n + 1 := by
    rcases l with _ | ⟨a, l⟩
    · simp [n] at hlead
    · simp [n]
  rw [lsum_eq] at hdom
  rw [ev_eq_sum x l (n + 1) hlen.le, sum_range_succ]
  have hx0 : 0 < x := by linarith
  have hq : 1 ≤ x / 4 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hS : ∑ i ∈ range n, |(l.getD i 0 : ℝ)| * x ^ i ≤
      (x / 4) ^ n * ∑ i ∈ range n, |(l.getD i 0 : ℝ)| * 4 ^ i := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := (mem_range.mp hi).le
    have : x ^ i = 4 ^ i * (x / 4) ^ i := by rw [← mul_pow]; congr 1; field_simp
    rw [this]
    have h1 : (x / 4) ^ i ≤ (x / 4) ^ n := pow_le_pow_right₀ hq hi'
    have h2 : (0 : ℝ) ≤ |(l.getD i 0 : ℝ)| * 4 ^ i := by positivity
    calc |(l.getD i 0 : ℝ)| * (4 ^ i * (x / 4) ^ i) = (|(l.getD i 0 : ℝ)| * 4 ^ i) * (x / 4) ^ i := by ring
      _ ≤ (|(l.getD i 0 : ℝ)| * 4 ^ i) * (x / 4) ^ n := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have hdom' : ∑ i ∈ range n, |(l.getD i 0 : ℝ)| * 4 ^ i < (l.getD n 0 : ℝ) * 4 ^ n := by
    have := (Int.cast_lt (R := ℝ)).mpr hdom
    push_cast [Int.cast_abs] at this
    exact this
  have hlow : -(∑ i ∈ range n, (|l.getD i 0| : ℝ) * x ^ i) ≤ ∑ i ∈ range n, (l.getD i 0 : ℝ) * x ^ i := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun i _ => ?_
    have : |(l.getD i 0 : ℝ) * x ^ i| = |(l.getD i 0 : ℝ)| * x ^ i := by
      rw [abs_mul, abs_of_pos (pow_pos hx0 _)]
    have := neg_abs_le ((l.getD i 0 : ℝ) * x ^ i)
    linarith
  have hxn : (l.getD n 0 : ℝ) * x ^ n = (x / 4) ^ n * ((l.getD n 0 : ℝ) * 4 ^ n) := by
    rw [show x ^ n = (x / 4) ^ n * 4 ^ n by rw [← mul_pow]; congr 1; field_simp]; ring
  have hpos : 0 < (x / 4) ^ n := pow_pos (by linarith) n
  have : (x / 4) ^ n * ∑ i ∈ range n, |(l.getD i 0 : ℝ)| * 4 ^ i < (l.getD n 0 : ℝ) * x ^ n := by
    rw [hxn]; exact mul_lt_mul_of_pos_left hdom' hpos
  linarith

/-! ### Reversal: `xⁿ · l(1/x) = (rev n l)(x)` -/

def rev (n : ℕ) (l : List ℤ) : List ℤ := (List.range (n + 1)).map fun i => l.getD (n - i) 0

theorem rev_getD (n : ℕ) (l : List ℤ) (i : ℕ) (hi : i < n + 1) : (rev n l).getD i 0 = l.getD (n - i) 0 := by
  simp [rev, List.getD_eq_getElem?_getD, hi]

theorem ev_rev {x : ℝ} (hx : x ≠ 0) (n : ℕ) {l : List ℤ} (hl : l.length ≤ n + 1) :
    x ^ n * ev (1 / x) l = ev x (rev n l) := by
  rw [ev_eq_sum _ l (n + 1) hl, ev_eq_sum _ (rev n l) (n + 1) (by simp [rev]), mul_sum]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [rev_getD n l i hi', show n + 1 - 1 - i = n - i by omega]
  rw [one_div, inv_pow]
  have : x ^ n = x ^ (n - i) * x ^ i := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

/-! ### Linear list operations (for constant congruences) -/

def padd : List ℤ → List ℤ → List ℤ
  | [], m => m
  | l, [] => l
  | a :: l, b :: m => (a + b) :: padd l m

def psmul (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

def pabs (l : List ℤ) : List ℤ := l.map (|·|)

theorem ev_padd (x : ℝ) : ∀ l m, ev x (padd l m) = ev x l + ev x m
  | [], m => by simp [padd, ev_nil]
  | a :: l, [] => by simp [padd, ev_nil]
  | a :: l, b :: m => by simp only [padd, ev_cons, ev_padd x l m]; push_cast; ring

theorem ev_psmul (x : ℝ) (c : ℤ) : ∀ l, ev x (psmul c l) = c * ev x l
  | [] => by simp [psmul, ev_nil]
  | a :: l => by
    simp only [psmul, List.map_cons] at *
    rw [ev_cons, ev_cons, show List.map (c * ·) l = psmul c l from rfl, ev_psmul x c l]
    push_cast; ring

theorem abs_ev_le (x : ℝ) (hx : 0 ≤ x) : ∀ l, |ev x l| ≤ ev x (pabs l)
  | [] => by simp [pabs, ev_nil]
  | a :: l => by
    simp only [pabs, List.map_cons] at *
    rw [ev_cons, ev_cons, show List.map (|·|) l = pabs l from rfl]
    have := abs_ev_le x hx l
    calc |(a : ℝ) + x * ev x l| ≤ |(a : ℝ)| + x * |ev x l| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hx]
      _ ≤ _ := by push_cast; gcongr

end LayerDT0

#print axioms LayerDT0.eq_zero_of_CB_eval
#print axioms LayerDT0.CB_mul
#print axioms LayerDT0.domPos_spec
#print axioms LayerDT0.ev_rev
#print axioms LayerDT0.abs_ev_le
