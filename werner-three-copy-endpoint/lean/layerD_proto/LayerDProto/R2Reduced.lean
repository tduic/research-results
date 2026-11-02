import LayerDProto.R2RedKernel
import LayerDProto.R2Families

/-!
# Layer D, (E′): soundness of the reduced-grid (literal-free) family totals

`R2RedKernel.lean` lets each chunk of a part claim only `redVal β N pos V`: the digits of its packed
`partD` value `V` at the reduced positions `pos`, packed again. This file proves that the unchanged family
check `familyZeroOK` on such claims, together with the orbit checks (`posOK`, `witSlice`) of the grid value, give
exactly the conclusion of `family_at_d_zero`: `Sym_H D` vanishes at **every** grid point of the grid value.

* `digitsAt_spec`: if `V = ∑_{j<N} a_j 2^(β j)` with `4 |a_j| < 2^β`, then `digitsAt β N pos V = pos.map a`.
* `chunk_red`: a reduced chunk value is `∑_k (fac ∑_{r ∈ chunk} F(r · gpt(pos[k]))) 2^(β k)`.
* `family_red_zero`: `familyZeroOK` on the reduced claims gives `Sym_H D (gpt(pos[k])) = 0` for every `k`
  (the total is `∑_k Sym_H D(gpt(pos[k])) 2^(β k)`, by `part_sym` per part, and its digits fit the width).
* `witOK_spec`, `maskOf_mem`: an orbit witness gives `q ∈ PF f` with `actF q (gpt j) = gpt c`, `c ∈ pos`;
  `witSlice_cover`: a checked slice of packed witnesses covers its positions.
* **`family_at_d_zeroR`**: the conclusion of `family_at_d_zero` (zero at every grid point `(t₀, t₁, S1[i₂], d)`)
  from the reduced checks, using that `Sym_H D` is `H`-invariant (`Sym.sym_act`).

Nothing about the reduction is assumed: the `H`-invariance is `SymReduce.sym_act`, the witnesses are
checked by the kernel.
-/

open Finset WernerEndpoint

namespace LayerDProto

/-! ## Digits at positions -/

theorem offs_eq (b n : ℕ) (hb : 1 ≤ b) : offs b n = ∑ i ∈ range n, 2 ^ (b - 1) * 2 ^ (b * i) := by
  unfold offs
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  simp_rw [pow_mul]
  rw [Nat.geomSum_eq h2 n]

theorem nat_digit (B : ℕ) (hB : 0 < B) : ∀ (N : ℕ) (u : ℕ → ℕ), (∀ i < N, u i < B) → ∀ j < N,
    (∑ i ∈ range N, u i * B ^ i) / B ^ j % B = u j := by
  intro N
  induction N with
  | zero => intro u _ j hj; omega
  | succ N ih =>
    intro u hu j hj
    rw [sum_range_succ']
    have e : ∑ i ∈ range N, u (i + 1) * B ^ (i + 1) = B * ∑ i ∈ range N, u (i + 1) * B ^ i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [e, pow_zero, mul_one]
    rcases j with _ | j
    · rw [pow_zero, Nat.div_one, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hu 0 (by omega))]
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, add_comm, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hu 0 (by omega)), zero_add]
      exact ih (fun i => u (i + 1)) (fun i hi => hu (i + 1) (by omega)) j (by omega)

theorem digitsAt_spec (β N : ℕ) (hβ : 1 ≤ β) (a : ℕ → ℤ) (D : ℕ) (ha : ∀ j < N, |a j| ≤ D)
    (hD : 4 * D < 2 ^ β) (pos : List ℕ) (hpos : ∀ j ∈ pos, j < N) :
    digitsAt β N pos (∑ j ∈ range N, a j * 2 ^ (β * j)) = pos.map a := by
  have hh : (2 : ℤ) ^ β = 2 * 2 ^ (β - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hD' : (4 * D : ℤ) < 2 ^ β := by exact_mod_cast hD
  have hlo : ∀ j < N, 0 ≤ a j + 2 ^ (β - 1) := by
    intro j hj
    have := ha j hj
    have := neg_abs_le (a j)
    have : (0 : ℤ) ≤ D := Nat.cast_nonneg _
    nlinarith
  have hhi : ∀ j < N, a j + 2 ^ (β - 1) < 2 ^ β := by
    intro j hj
    have := ha j hj
    have := le_abs_self (a j)
    have : (0 : ℤ) ≤ D := Nat.cast_nonneg _
    nlinarith
  set u : ℕ → ℕ := fun j => (a j + 2 ^ (β - 1)).toNat with hu
  have hu' : ∀ j < N, (u j : ℤ) = a j + 2 ^ (β - 1) := fun j hj => Int.toNat_of_nonneg (hlo j hj)
  have hUz : (∑ j ∈ range N, a j * 2 ^ (β * j)) + Int.ofNat (offs β N) =
      ((∑ j ∈ range N, u j * (2 ^ β) ^ j : ℕ) : ℤ) := by
    rw [Int.ofNat_eq_coe, offs_eq β N hβ]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [hu' j (mem_range.mp hj), ← pow_mul]
    ring
  unfold digitsAt
  simp only
  rw [hUz, Int.toNat_natCast]
  refine List.map_congr_left fun j hj => ?_
  have hjN := hpos j hj
  rw [Nat.shiftRight_eq_div_pow, pow_mul,
    nat_digit (2 ^ β) (by positivity) N u (fun i hi => by
      have h1 : ((u i : ℕ) : ℤ) < ((2 ^ β : ℕ) : ℤ) := by push_cast; rw [hu' i hi]; exact hhi i hi
      exact_mod_cast h1) j hjN,
    Int.subNatNat_eq_coe, hu' j hjN]
  push_cast
  ring

/-! ## Grid positions -/

/-- The grid point of position `j = (t₀ · 24 + t₁) |S1| + i₂`. -/
noncomputable def gptJ (S1 : List ℕ) (d j : ℕ) : Tup (Fin 3) :=
  gpt S1 d (j / (24 * S1.length)) (j / S1.length % 24) (j % S1.length)

theorem gptJ_enc (S1 : List ℕ) (d t0 t1 i2 : ℕ) (ht1 : t1 < 24) (hi2 : i2 < S1.length) :
    gptJ S1 d ((t0 * 24 + t1) * S1.length + i2) = gpt S1 d t0 t1 i2 := by
  obtain ⟨d0, d1, d2⟩ := enc3_digits (k1 := 24) (k2 := S1.length) (a0 := t0) ht1 hi2
  simp only [enc3] at d0 d1 d2
  rw [gptJ, d0, d1, d2]

theorem repVal_eqJ (P : PartData) (k0 k1 k2 kq : ℕ) (hks : P.ks = [k0, k1, k2, kq]) (β : ℕ) (S1 : List ℕ)
    (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24) (p : KPar) (hp : p.ok) (hσ : p.1 ∈ perms3) :
    repVal β k0 k1 k2 kq P.rhos (Ymat P.k P.X P.Bl P.Br) S1 d p =
      ∑ j ∈ range (24 * 24 * S1.length), FTP P (actF (toH p) (gptJ S1 d j)) * 2 ^ (β * j) :=
  (repVal_eq P k0 k1 k2 kq hks β S1 hS1 d hd p hp hσ).trans (grid_sum_eq _ _ _)

theorem mem_repsOf (gs : List MGroup) (r : KPar) (h : r ∈ repsOf gs) :
    ∃ mg ∈ gs, ∃ sg ∈ mg.2, r ∈ sg.2 := by
  simp only [repsOf, List.mem_flatMap] at h
  obtain ⟨mg, hmg, sg, hsg, hr⟩ := h
  exact ⟨mg, hmg, sg, hsg, hr⟩

theorem sum_map_const_le {α : Type*} (l : List α) (g : α → ℤ) (B : ℤ) (h : ∀ x ∈ l, |g x| ≤ B) :
    |(l.map g).sum| ≤ l.length * B := by
  refine (abs_list_sum_le l g (fun _ => B) h).trans ?_
  simp [List.map_const', List.sum_replicate]

/-- **One reduced chunk.** -/
theorem chunk_red (P : PartData) (β : ℕ) (hβ : 1 ≤ β) (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ)
    (hd : d < 24) (pos : List ℕ) (hpos : ∀ j ∈ pos, j < 24 * 24 * S1.length) (D : ℕ) (hDβ : 4 * D < 2 ^ β)
    (hBl : ∀ r ∈ P.Bl, r.length = P.k) (hBr : ∀ r ∈ P.Br, r.length = P.k)
    (gs : List MGroup) (hgsD : P.fac.natAbs * (repsOf gs).length * Fbound P ≤ D) (L : ℤ)
    (h : partDR β P.w P.bnd P.ks P.k P.X P.Bl P.Br P.fac P.rhos d S1 gs pos = some L) :
    L = ∑ k ∈ range pos.length, (P.fac * ((repsOf gs).map fun r =>
      FTP P (actF (toH r) (gptJ S1 d (pos.getD k 0)))).sum) * 2 ^ (β * k) := by
  unfold partDR at h
  obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨k0, k1, k2, kq, hks, hpar, hv⟩ := partD_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hV
  set N := 24 * 24 * S1.length
  set a : ℕ → ℤ := fun j => P.fac * ((repsOf gs).map fun r => FTP P (actF (toH r) (gptJ S1 d j))).sum with ha
  have hVa : V = ∑ j ∈ range N, a j * 2 ^ (β * j) := by
    rw [hv, repsOf_sum]
    have e : ((repsOf gs).map (repVal β k0 k1 k2 kq P.rhos (Ymat P.k P.X P.Bl P.Br) S1 d)) =
        (repsOf gs).map fun r => ∑ j ∈ range N, FTP P (actF (toH r) (gptJ S1 d j)) * 2 ^ (β * j) := by
      refine List.map_congr_left fun r hr => ?_
      obtain ⟨mg, hmg, sg, hsg, hr'⟩ := mem_repsOf gs r hr
      obtain ⟨h1, h2⟩ := hpar mg hmg sg hsg r hr'
      exact repVal_eqJ P k0 k1 k2 kq hks β S1 hS1 d hd r h1 h2
    rw [e, ← sum_list_comm, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [ha]
    simp only
    rw [List.sum_map_mul_right]
    ring
  have hab : ∀ j < N, |a j| ≤ D := by
    intro j _
    rw [ha]
    simp only
    rw [abs_mul]
    have h1 := sum_map_const_le (repsOf gs) (fun r => FTP P (actF (toH r) (gptJ S1 d j))) (Fbound P)
      (fun r _ => FTP_bound P hBl hBr _)
    have h2 : (P.fac.natAbs : ℤ) * ((repsOf gs).length * (Fbound P : ℤ)) ≤ D := by
      have := hgsD
      rw [← mul_assoc]; exact_mod_cast this
    rw [Int.abs_eq_natAbs]
    calc (P.fac.natAbs : ℤ) * |((repsOf gs).map fun r => FTP P (actF (toH r) (gptJ S1 d j))).sum|
        ≤ (P.fac.natAbs : ℤ) * ((repsOf gs).length * (Fbound P : ℤ)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ D := h2
  unfold redVal
  rw [hVa, digitsAt_spec β N hβ a D hab hDβ pos hpos, pkB_eq, pk_eq, List.length_map]
  refine sum_congr rfl fun k hk => ?_
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact mem_range.mp hk), List.getElem_map,
    List.getD_eq_getElem _ _ (mem_range.mp hk)]

/-! ## The family at the reduced positions -/

theorem le_foldl_sum_of_mem (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.foldl (· + ·) 0 := by
  rw [foldl_add_sum_nat, zero_add]
  exact List.le_sum_of_mem h

theorem length_repsOf_le (Q : PartAtD) (hflat : Q.chunks.flatMap (fun c => repsOf c.1) = Q.reps)
    (c : List MGroup × ℤ) (hc : c ∈ Q.chunks) : (repsOf c.1).length ≤ Q.reps.length := by
  rw [← hflat, List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- **The family at the reduced positions.** `familyZeroOK` on reduced chunk claims gives
`Sym_H D = 0` at the grid point of every reduced position. -/
theorem family_red_zero {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (β : ℕ) (hβ : 1 ≤ β) (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24)
    (pos : List ℕ) (hpos : ∀ j ∈ pos, j < 24 * 24 * S1.length)
    (parts : List (PartData × PartAtD))
    (hstat : ∀ x ∈ parts, partStaticOK bosL x.1 = true) (hat : ∀ x ∈ parts, partAtDOK bosL x.1 x.2 = true)
    (hD : ∀ x ∈ parts, ∀ c ∈ x.2.chunks,
      partDR β x.1.w x.1.bnd x.1.ks x.1.k x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos d S1 c.1 pos = some c.2)
    (hfam : familyZeroOK β parts = true) :
    ∀ k < pos.length, ∑ p : PF f,
      (parts.map fun x => x.1.fac * FTP x.1 (actF p.1 (gptJ S1 d (pos.getD k 0)))).sum = 0 := by
  simp only [familyZeroOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfam
  obtain ⟨htot0, hB4⟩ := hfam
  set g : ℕ → Tup (Fin 3) := fun k => gptJ S1 d (pos.getD k 0) with hg
  set SD : Tup (Fin 3) → ℤ := fun t => ∑ p : PF f, (parts.map fun x => x.1.fac * FTP x.1 (actF p.1 t)).sum
    with hSD
  set SymP : PartData → Tup (Fin 3) → ℤ := fun P t => ∑ p : PF f, FTP P (actF p.1 t) with hSymP
  have hSDP : ∀ t, SD t = (parts.map fun x => x.1.fac * SymP x.1 t).sum := fun t => by
    simp only [hSD, hSymP]
    rw [sum_list_comm]
    exact congrArg List.sum (List.map_congr_left fun x _ => (mul_sum _ _ _).symm)
  -- one part: `|K| ∑_chunks L = ∑_k fac Sym F (g k) 2^(β k)`
  have hpart : ∀ x ∈ parts, (x.1.Ks.length : ℤ) * (x.2.chunks.map (·.2)).sum =
      ∑ k ∈ range pos.length, x.1.fac * SymP x.1 (g k) * 2 ^ (β * k) := by
    intro x hx
    obtain ⟨-, hBl, hBr, hclos, -⟩ := partStaticOK_spec bosL x.1 (hstat x hx)
    obtain ⟨-, hflat⟩ := partAtDOK_spec bosL x.1 x.2 (hat x hx)
    have hc : ∀ c ∈ x.2.chunks, c.2 = ∑ k ∈ range pos.length, (x.1.fac * ((repsOf c.1).map fun r =>
        FTP x.1 (actF (toH r) (g k))).sum) * 2 ^ (β * k) := by
      intro c hc
      refine chunk_red x.1 β hβ S1 hS1 d hd pos hpos (famBound parts) hB4 hBl hBr c.1 ?_ c.2 (hD x hx c hc)
      have hK : 1 ≤ x.1.Ks.length := by
        simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hclos
        omega
      calc x.1.fac.natAbs * (repsOf c.1).length * Fbound x.1
          ≤ x.1.fac.natAbs * x.1.Ks.length * x.2.reps.length * Fbound x.1 := by
            have := length_repsOf_le x.2 hflat c hc
            have h1 : (repsOf c.1).length ≤ x.1.Ks.length * x.2.reps.length := by nlinarith
            calc x.1.fac.natAbs * (repsOf c.1).length * Fbound x.1
                ≤ x.1.fac.natAbs * (x.1.Ks.length * x.2.reps.length) * Fbound x.1 := by gcongr
              _ = _ := by ring
        _ ≤ famBound parts := le_foldl_sum_of_mem _ _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [List.map_congr_left hc, ← sum_list_comm, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [List.sum_map_mul_right, List.sum_map_mul_left]
    have e : (x.2.chunks.map fun c => ((repsOf c.1).map fun r => FTP x.1 (actF (toH r) (g k))).sum).sum =
        (x.2.reps.map fun r => FTP x.1 (actF (toH r) (g k))).sum := by
      rw [← hflat, List.map_flatMap, flatMap_sum]
    rw [e, hSymP]
    simp only
    rw [part_sym bosL hbos hcomp hnd x.1 x.2 (hstat x hx) (hat x hx),
      list_sum_range x.2.reps _ ([], false, 0, 0)]
    ring
  -- the family total
  have htot : famTotal parts = ∑ k ∈ range pos.length, SD (g k) * 2 ^ (β * k) := by
    unfold famTotal
    rw [foldl_add_sum, zero_add]
    have e : (parts.map fun x => (x.1.Ks.length : ℤ) * (x.2.chunks.map (·.2)).foldl (· + ·) 0) =
        parts.map fun x => ∑ k ∈ range pos.length, x.1.fac * SymP x.1 (g k) * 2 ^ (β * k) :=
      List.map_congr_left fun x hx => by rw [foldl_add_sum, zero_add]; exact hpart x hx
    rw [e, ← sum_list_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [hSDP, ← List.sum_map_mul_right]
  -- the bound of the true digits
  have hSDb : ∀ t, |SD t| ≤ (famBound parts : ℤ) := by
    intro t
    rw [hSDP]
    unfold famBound
    rw [foldl_add_sum_nat, zero_add, Nat.cast_list_sum, List.map_map]
    refine abs_list_sum_le _ _ _ fun x hx => ?_
    obtain ⟨-, hBl, hBr, -, -⟩ := partStaticOK_spec bosL x.1 (hstat x hx)
    simp only [Function.comp, hSymP]
    rw [part_sym bosL hbos hcomp hnd x.1 x.2 (hstat x hx) (hat x hx), abs_mul, abs_mul]
    push_cast
    rw [Int.abs_eq_natAbs x.1.fac, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc, mul_assoc]
    gcongr
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun j _ => FTP_bound x.1 hBl hBr _).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
  have hdig := digits_of_eq β pos.length (fun k => SD (g k)) (fun _ => 0) (famBound parts) 0
    (fun k _ => hSDb _) (fun k _ => by simp) hB4 (by simp)
    (by rw [← htot, htot0]; simp)
  intro k hk
  exact hdig k hk

/-! ## Orbit witnesses -/

theorem maskOf_mem (l : List ℕ) (c : ℕ) (h : (maskOf l >>> c) % 2 = 1) : c ∈ l := by
  have ht : Nat.testBit (maskOf l) c = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, ← Nat.shiftRight_eq_div_pow]; exact h
  clear h
  induction l with
  | nil => simp [maskOf] at ht
  | cons a l ih =>
    simp only [maskOf, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq] at ht
    rcases ht with h | h
    · exact List.mem_cons_of_mem _ (ih h)
    · rw [h]; exact List.mem_cons_self

theorem mod_div_mod (W a b c : ℕ) (h : a + c ≤ b) : W % 2 ^ b / 2 ^ a % 2 ^ c = W / 2 ^ a % 2 ^ c := by
  have hb : 2 ^ b = 2 ^ a * (2 ^ c * 2 ^ (b - a - c)) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hW : W = W % 2 ^ b + 2 ^ a * (2 ^ c * (2 ^ (b - a - c) * (W / 2 ^ b))) := by
    conv_lhs => rw [← Nat.mod_add_div W (2 ^ b)]
    rw [hb]; ring
  conv_rhs => rw [hW, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem witLin_spec (bosL S1 : List ℕ) (d N mask : ℕ) :
    ∀ (n j W : ℕ), witLin bosL S1 d N mask j n W = true →
      ∀ i < n, witOK bosL S1 d N mask (j + i) (W / 2 ^ (32 * i) % 2 ^ 32) = true
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, j, W, h, i, hi => by
    simp only [witLin, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := witLin_spec bosL S1 d N mask n (j + 1) (W >>> 32) h.2 i (by omega)
      rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add] at this
      rw [show j + (i + 1) = j + 1 + i by omega, show 32 * (i + 1) = 32 + 32 * i by ring]
      exact this

theorem witSlice_spec (bosL S1 : List ℕ) (d N mask : ℕ) :
    ∀ (f j n W : ℕ), witSlice bosL S1 d N mask f j n W = true →
      ∀ i < n, witOK bosL S1 d N mask (j + i) (W / 2 ^ (32 * i) % 2 ^ 32) = true
  | 0, j, n, W, h => witLin_spec bosL S1 d N mask n j W h
  | f + 1, j, n, W, h => by
    unfold witSlice at h
    split at h
    · exact witLin_spec bosL S1 d N mask n j W h
    · simp only [Bool.and_eq_true] at h
      intro i hi
      rcases Nat.lt_or_ge i (n / 2) with hl | hl
      · have := witSlice_spec bosL S1 d N mask f j (n / 2) _ h.1 i hl
        rwa [mod_div_mod W (32 * i) (32 * (n / 2)) 32 (by omega)] at this
      · have := witSlice_spec bosL S1 d N mask f (j + n / 2) (n - n / 2) _ h.2 (i - n / 2) (by omega)
        rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add,
          show 32 * (n / 2) + 32 * (i - n / 2) = 32 * i by omega, show j + n / 2 + (i - n / 2) = j + i by omega]
          at this
        exact this

/-- A checked slice of witnesses covers its positions. -/
theorem witSlice_cover (bosL S1 : List ℕ) (d N mask f j0 n W : ℕ)
    (h : witSlice bosL S1 d N mask f j0 n W = true) :
    ∀ j, j0 ≤ j → j < j0 + n → ∃ e, witOK bosL S1 d N mask j e = true := by
  intro j h1 h2
  have := witSlice_spec bosL S1 d N mask f j0 n W h (j - j0) (by omega)
  rw [show j0 + (j - j0) = j by omega] at this
  exact ⟨_, this⟩

theorem nth_perms3_mem : ∀ i < 6, nth perms3 i [0, 1, 2] ∈ perms3 := by decide

theorem gridIdx_lt (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (j : ℕ) (hj : j < 24 * 24 * S1.length) :
    j / (24 * S1.length) < 24 ∧ j / S1.length % 24 < 24 ∧ nth S1 (j % S1.length) 0 < 24 ∧
      j % S1.length < S1.length := by
  have hs : 0 < S1.length := by
    rcases Nat.eq_zero_or_pos S1.length with h | h
    · rw [h] at hj; omega
    · exact h
  have hi : j % S1.length < S1.length := Nat.mod_lt _ hs
  refine ⟨?_, Nat.mod_lt _ (by norm_num), ?_, hi⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]; linarith
  · rw [nth_eq_getD, List.getD_eq_getElem _ _ hi]; exact hS1 _ (List.getElem_mem _)

/-- The index tuple of `gptJ`. -/
theorem gptJ_eq (S1 : List ℕ) (d j : ℕ) :
    gptJ S1 d j = tupEquiv (![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)], fin24 d) := by
  simp only [gptJ, gpt, gridIdx, nth_eq_getD S1 (j % S1.length) 0]
  rfl

/-- **An orbit witness** gives an element of the family's group moving the grid point of `j` to the
grid point of `c`. -/
theorem witOK_spec {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24) (mask j e : ℕ)
    (hj : j < 24 * 24 * S1.length) (h : witOK bosL S1 d (24 * 24 * S1.length) mask j e = true) :
    ∃ q : PF f, ∃ c, c < 24 * 24 * S1.length ∧ (mask >>> c) % 2 = 1 ∧
      actF q.1 (gptJ S1 d j) = gptJ S1 d c := by
  simp only [witOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsi, hg⟩, hg'⟩, hc⟩, hm⟩, e0⟩, e1⟩, e2⟩, eq⟩ := h
  set p := witPar (e / 32768) with hp
  set c := e % 32768
  have hσ : p.1 ∈ perms3 := nth_perms3_mem _ hsi
  have hpok : p.ok := ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩
  obtain ⟨hg24, hgb⟩ := hbos _ hg
  obtain ⟨hg'24, hg'b⟩ := hbos _ hg'
  refine ⟨⟨toH p, by rw [toH_g p hg24]; exact hgb, by rw [toH_g' p hg'24]; exact hg'b⟩, c, hc, hm, ?_⟩
  simp only
  rw [gptJ_eq S1 d j, gptJ_eq S1 d c]
  have hsym := tupEquiv_actIdx (toI p) (![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)], fin24 d)
  rw [show toH p = toHPar (toI p) from rfl, ← hsym]
  congr 1
  obtain ⟨hA, hB⟩ := actIdx_toI p hpok hσ (![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)], fin24 d)
  obtain ⟨j0, j1, j2, -⟩ := gridIdx_lt S1 hS1 j hj
  obtain ⟨c0, c1, c2, -⟩ := gridIdx_lt S1 hS1 c hc
  have ej : [((![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)] : Fin 3 → Fin 24) 0 : ℕ),
      ((![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)] : Fin 3 → Fin 24) 1 : ℕ),
      ((![fin24 (nth (gridIdx S1 j) 0 0), fin24 (nth (gridIdx S1 j) 1 0),
      fin24 (nth (gridIdx S1 j) 2 0)] : Fin 3 → Fin 24) 2 : ℕ)] = gridIdx S1 j := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, fin24, gridIdx, nth] at j0 j1 j2 ⊢
    rw [Nat.mod_eq_of_lt j0, Nat.mod_eq_of_lt j1, Nat.mod_eq_of_lt j2]
  rw [ej] at hA
  refine Prod.ext (funext fun i => Fin.ext ?_) (Fin.ext ?_)
  · rw [hA i]
    fin_cases i
    · show kact p (nth (gridIdx S1 j) (nth p.1 0 0) 0) = nth (gridIdx S1 c) 0 0 % 24
      rw [Nat.mod_eq_of_lt (show nth (gridIdx S1 c) 0 0 < 24 from c0)]; exact e0
    · show kact p (nth (gridIdx S1 j) (nth p.1 1 0) 0) = nth (gridIdx S1 c) 1 0 % 24
      rw [Nat.mod_eq_of_lt (show nth (gridIdx S1 c) 1 0 < 24 from c1)]; exact e1
    · show kact p (nth (gridIdx S1 j) (nth p.1 2 0) 0) = nth (gridIdx S1 c) 2 0 % 24
      rw [Nat.mod_eq_of_lt (show nth (gridIdx S1 c) 2 0 < 24 from c2)]; exact e2
  · rw [hB]
    simp only [fin24, Nat.mod_eq_of_lt hd]
    exact eq

/-! ## The reduced family check at one grid value -/

/-- **`family_at_d_zero` from the reduced checks.** The parts' reduced chunk claims (`partDR`), the
unchanged family check `familyZeroOK` and the orbit checks (`posOK`, `witSlice_cover`) give `Sym_H D = 0` at every grid point
`(t₀, t₁, S1[i₂], d)`, the hypothesis `hzero` of `family_zero` / `famZero_of_grid`. -/
theorem family_at_d_zeroR {f : Fam} (bosL : List ℕ) (hbos : ∀ c ∈ bosL, ∃ h : c < 24, permTab ⟨c, h⟩ ∈ bos f)
    (hcomp : ∀ c : Fin 24, permTab c ∈ bos f → (c : ℕ) ∈ bosL) (hnd : (hcodes bosL).Nodup)
    (β : ℕ) (hβ : 1 ≤ β) (S1 : List ℕ) (hS1 : ∀ x ∈ S1, x < 24) (d : ℕ) (hd : d < 24)
    (pos : List ℕ) (mask : ℕ) (hposOK : posOK S1 pos mask = true)
    (hcov : ∀ j < 24 * 24 * S1.length, ∃ e, witOK bosL S1 d (24 * 24 * S1.length) mask j e = true)
    (Ps : List PartData) (Qs : List PartAtD) (hlen : Ps.length = Qs.length)
    (hstat : ∀ x ∈ Ps.zip Qs, partStaticOK bosL x.1 = true) (hat : ∀ x ∈ Ps.zip Qs, partAtDOK bosL x.1 x.2 = true)
    (hD : ∀ x ∈ Ps.zip Qs, ∀ c ∈ x.2.chunks,
      partDR β x.1.w x.1.bnd x.1.ks x.1.k x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos d S1 c.1 pos = some c.2)
    (hfam : familyZeroOK β (Ps.zip Qs) = true) :
    ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < S1.length,
      ∑ p : PF f, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt S1 d t0 t1 i2))).sum = 0 := by
  simp only [posOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hposOK
  obtain ⟨hmask, hposN⟩ := hposOK
  set N := 24 * 24 * S1.length
  have e : (Ps.zip Qs).map Prod.fst = Ps := List.map_fst_zip (le_of_eq hlen)
  set D : Tup (Fin 3) → ℤ := fun t => (Ps.map fun P => P.fac * FTP P t).sum with hDdef
  have hDz : ∀ t, ((Ps.zip Qs).map fun x => x.1.fac * FTP x.1 t).sum = D t := fun t => by
    rw [hDdef]; simp only; conv_rhs => rw [← e]
    rw [List.map_map]; rfl
  have hred := family_red_zero bosL hbos hcomp hnd β hβ S1 hS1 d hd pos (fun j hj => hposN j hj) (Ps.zip Qs)
    hstat hat hD hfam
  simp only [hDz] at hred
  -- every grid position
  have hall : ∀ j < N, ∑ p : PF f, D (actF p.1 (gptJ S1 d j)) = 0 := by
    intro j hj
    obtain ⟨e, hw⟩ := hcov j hj
    obtain ⟨q, c, hc, hm, hq⟩ := witOK_spec (f := f) bosL hbos S1 hS1 d hd mask j _ hj hw
    have hcp : c ∈ pos := maskOf_mem pos c (by rw [hmask]; exact hm)
    obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem hcp
    have h0 := hred k hk
    rw [List.getD_eq_getElem _ _ hk, hkc, ← hq] at h0
    rw [← h0]
    exact (Sym.sym_act (fun p : PF f => actF p.1) mulPF (fun p q t => actF_mul p.1 q.1 t) mulPF_bijective
      D q (gptJ S1 d j)).symm
  intro t0 ht0 t1 ht1 i2 hi2
  have hj : (t0 * 24 + t1) * S1.length + i2 < N := by
    have := enc3_lt (k0 := 24) (k1 := 24) (k2 := S1.length) ht0 ht1 hi2
    simp only [enc3] at this; exact this
  have := hall _ hj
  rwa [gptJ_enc S1 d t0 t1 i2 ht1 hi2] at this

end LayerDProto

#print axioms LayerDProto.digitsAt_spec
#print axioms LayerDProto.chunk_red
#print axioms LayerDProto.family_red_zero
#print axioms LayerDProto.witOK_spec
#print axioms LayerDProto.witSlice_cover
#print axioms LayerDProto.family_at_d_zeroR
