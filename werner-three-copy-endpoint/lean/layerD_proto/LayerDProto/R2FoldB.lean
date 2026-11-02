import LayerDProto.R2Fold

/-!
# Layer D, (E′): soundness of the packed `B`-level fold check (`foldBOK`)

`foldBOK_spec`: if `foldBOK` succeeds, the folded matrix of `Y = B_l X B_rᵀ` (`foldW`, at the axis-permuted
rows `pidx`) is `α Y`.
-/

open Finset

namespace LayerDProto

theorem nth_range_map {α : Type} (g : ℕ → α) (d : α) (m u : ℕ) (hu : u < m) :
    nth ((List.range m).map g) u d = g u := by
  rw [nth_eq_getD, List.getD_eq_getElem _ d (by simpa using hu)]
  simp

theorem pk_row (w k : ℕ) (B : List (List ℤ)) (hB : ∀ r ∈ B, r.length = k) (i : ℕ) (hi : i < B.length) :
    pk w (B.getD i []) = ∑ p ∈ range k, ent B i p * 2 ^ (w * p) := by
  rw [pk_eq, hB _ (by rw [List.getD_eq_getElem _ [] hi]; exact List.getElem_mem _)]
  rfl

theorem pidx_lt (k0 k1 k2 kq : ℕ) (σ : List ℕ) (hσ : σ ∈ perms3) (c : D4T) (hc : c ∈ D4 k0 k1 k2 kq) :
    pidx k0 k1 k2 kq σ c < k0 * k1 * k2 * kq := by
  obtain ⟨il, ib⟩ := permIdx3_props k0 k1 k2 kq σ hσ
  simp only [D4, mem_product, mem_range] at hc
  obtain ⟨h0, h1, h2, h3⟩ := hc
  have he := enc3_lt h0 h1 h2
  have hm : (permIdx3 [k0, k1, k2, kq] σ).getD (enc3 k1 k2 c.1 c.2.1 c.2.2.1) 0 < k0 * k1 * k2 := by
    rw [List.getD_eq_getElem _ 0 (by rw [il]; exact he)]
    exact ib _ (List.getElem_mem _)
  unfold pidx
  have : ((permIdx3 [k0, k1, k2, kq] σ).getD (enc3 k1 k2 c.1 c.2.1 c.2.2.1) 0 + 1) * kq ≤ k0 * k1 * k2 * kq :=
    Nat.mul_le_mul_right kq hm
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Soundness of `foldBOK`.** -/
theorem foldBOK_spec (w k0 k1 k2 kq k : ℕ) (X Bl Br : List (List ℤ)) (κ : KPar) (τ : Bool)
    (As Cs : List (List (List ℤ))) (als : List ℤ) (Q R : List (List ℤ))
    (h : foldBOK w [k0, k1, k2, kq] k X Bl Br κ τ As Cs als Q R = true) :
    nth als 0 0 * nth als 1 0 * nth als 2 0 * nth als 3 0 ≠ 0 ∧
    0 < k0 ∧ 0 < k1 ∧ 0 < k2 ∧ 0 < kq ∧ κ.1 ∈ perms3 ∧
    (∀ u < 3, nth [k0, k1, k2, kq] (nth (inv3 κ.1) u 0) 1 = nth [k0, k1, k2, kq] u 1) ∧
    ∀ a ∈ D4 k0 k1 k2 kq, ∀ b ∈ D4 k0 k1 k2 kq,
      foldW k0 k1 k2 kq (ent (nth As 0 [])) (ent (nth As 1 [])) (ent (nth As 2 [])) (ent (nth As 3 []))
        (ent (nth Cs 0 [])) (ent (nth Cs 1 [])) (ent (nth Cs 2 [])) (ent (nth Cs 3 []))
        (fun c e => Ymat k X Bl Br (pidx k0 k1 k2 kq κ.1 c) (pidx k0 k1 k2 kq κ.1 e))
        (if τ then b else a) (if τ then a else b) =
      (nth als 0 0 * nth als 1 0 * nth als 2 0 * nth als 3 0) * Ymat k X Bl Br (enc4 k1 k2 kq a) (enc4 k1 k2 kq b) := by
  unfold foldBOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, hσ, hal0, hdim, -, -, hAC, hX, hBl, hBr, hQ, hR, hdL, hdG, hdB, hdX, hE1, hE2, hEX⟩ := h
  refine ⟨hal0, h0, h1, h2, h3, hσ, hdim, fun a ha b hb => ?_⟩
  set al := nth als 0 0 * nth als 1 0 * nth als 2 0 * nth als 3 0 with hal
  set n := k0 * k1 * k2 * kq with hn
  set ks := [k0, k1, k2, kq] with hks
  obtain ⟨hXl, hXr⟩ := isRect_spec _ _ _ hX
  obtain ⟨hBll, hBlr⟩ := isRect_spec _ _ _ hBl
  obtain ⟨hBrl, hBrr⟩ := isRect_spec _ _ _ hBr
  obtain ⟨hQl, hQr⟩ := isRect_spec _ _ _ hQ
  obtain ⟨hRl, hRr⟩ := isRect_spec _ _ _ hR
  have hA : ∀ u < 4, (nth As u []).length = nth ks u 1 ∧ ∀ r ∈ nth As u [], r.length = nth ks u 1 :=
    fun u hu => isRect_spec _ _ _ (hAC u hu).1
  have hC : ∀ u < 4, (nth Cs u []).length = nth ks u 1 ∧ ∀ r ∈ nth Cs u [], r.length = nth ks u 1 :=
    fun u hu => isRect_spec _ _ _ (hAC u hu).2
  set Cts := (List.range 4).map fun u => transp (nth ks u 1) (nth Cs u []) with hCtsdef
  have hCt : ∀ u < 4, nth Cts u [] = transp (nth ks u 1) (nth Cs u []) := fun u hu => nth_range_map _ _ 4 u hu
  have hCtl : ∀ u < 4, (nth Cts u []).length = nth ks u 1 := fun u hu => by
    rw [hCt u hu]; exact (transp_spec _ _ (hC u hu).2).1
  have hCtE : ∀ u < 4, ∀ x < nth ks u 1, ∀ y, ent (nth Cts u []) x y = ent (nth Cs u []) y x := fun u hu x hx y => by
    rw [hCt u hu]; exact ent_transp _ _ (hC u hu).2 x y hx
  have hpid := pidx_lt k0 k1 k2 kq κ.1 hσ
  -- the packed folds
  obtain ⟨-, LBs⟩ := foldRows_spec w k0 k1 k2 kq h0 h1 h2 h3 κ.1 hσ As (fun u hu => (hA u hu).1) Bl
  obtain ⟨-, GBs⟩ := foldRows_spec w k0 k1 k2 kq h0 h1 h2 h3 κ.1 hσ Cts hCtl Br
  set LBf : D4T → ℕ → ℤ := fun a p => ∑ c ∈ D4 k0 k1 k2 kq, ent (nth As 0 []) c.1 a.1 * ent (nth As 1 []) c.2.1 a.2.1 *
    ent (nth As 2 []) c.2.2.1 a.2.2.1 * ent (nth As 3 []) c.2.2.2 a.2.2.2 * ent Bl (pidx k0 k1 k2 kq κ.1 c) p with hLBf
  set GBf : D4T → ℕ → ℤ := fun a p => ∑ c ∈ D4 k0 k1 k2 kq, ent (nth Cts 0 []) c.1 a.1 * ent (nth Cts 1 []) c.2.1 a.2.1 *
    ent (nth Cts 2 []) c.2.2.1 a.2.2.1 * ent (nth Cts 3 []) c.2.2.2 a.2.2.2 * ent Br (pidx k0 k1 k2 kq κ.1 c) p with hGBf
  have hpack : ∀ (As' : List (List (List ℤ))) (B : List (List ℤ)), (∀ r ∈ B, r.length = k) → B.length = n →
      ∀ a : D4T, ∑ c ∈ D4 k0 k1 k2 kq, ent (nth As' 0 []) c.1 a.1 * ent (nth As' 1 []) c.2.1 a.2.1 *
        ent (nth As' 2 []) c.2.2.1 a.2.2.1 * ent (nth As' 3 []) c.2.2.2 a.2.2.2 *
        pk w (B.getD (pidx k0 k1 k2 kq κ.1 c) []) =
      ∑ p ∈ range k, (∑ c ∈ D4 k0 k1 k2 kq, ent (nth As' 0 []) c.1 a.1 * ent (nth As' 1 []) c.2.1 a.2.1 *
        ent (nth As' 2 []) c.2.2.1 a.2.2.1 * ent (nth As' 3 []) c.2.2.2 a.2.2.2 *
        ent B (pidx k0 k1 k2 kq κ.1 c) p) * 2 ^ (w * p) := by
    intro As' B hB hBn a
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun c hc => ?_
    rw [pk_row w k B hB _ (by rw [hBn]; exact hpid c hc), mul_sum]
    refine sum_congr rfl fun p _ => ?_
    ring
  have hLB : ∀ a ∈ D4 k0 k1 k2 kq, (foldRows w ks κ.1 As Bl).getD (enc4 k1 k2 kq a) 0 =
      ∑ p ∈ range k, LBf a p * 2 ^ (w * p) := fun a ha => by
    rw [LBs a ha, hpack As Bl hBlr hBll a]
  have hGB : ∀ a ∈ D4 k0 k1 k2 kq, (foldRows w ks κ.1 Cts Br).getD (enc4 k1 k2 kq a) 0 =
      ∑ p ∈ range k, GBf a p * 2 ^ (w * p) := fun a ha => by
    rw [GBs a ha, hpack Cts Br hBrr hBrl a]
  -- bounds of the folded digits
  have hLBb : ∀ a p, |LBf a p| ≤ (((n * (entMax (nth As 0 []) * entMax (nth As 1 []) * entMax (nth As 2 []) *
      entMax (nth As 3 [])) * (entMax Bl + entMax Br) : ℕ) : ℤ)) := by
    intro a p
    refine (bound_D4 k0 k1 k2 kq _ _ fun c _ => abs_ent4 _ _ _ _ Bl _ _ _ _ _ _ _ _ _ _).trans ?_
    rw [← hn]
    push_cast
    rw [← mul_assoc]
    gcongr
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hGBb : ∀ a p, |GBf a p| ≤ (((n * (entMax (nth Cts 0 []) * entMax (nth Cts 1 []) * entMax (nth Cts 2 []) *
      entMax (nth Cts 3 [])) * (entMax Bl + entMax Br) : ℕ) : ℤ)) := by
    intro a p
    refine (bound_D4 k0 k1 k2 kq _ _ fun c _ => abs_ent4 _ _ _ _ Br _ _ _ _ _ _ _ _ _ _).trans ?_
    rw [← hn]
    push_cast
    rw [← mul_assoc]
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  -- the right-hand products
  set BQ : ℕ → ℕ → ℤ := fun i p => ∑ q ∈ range k, ent Bl i q * ent Q p q with hBQ
  set BR : ℕ → ℕ → ℤ := fun i p => ∑ q ∈ range k, ent Br i q * ent R p q with hBR
  have hBQb : ∀ i p, |BQ i p| ≤ (((rowSumMax Bl + rowSumMax Br) * (entMax Q + entMax R) : ℕ) : ℤ) := by
    intro i p
    calc |BQ i p| ≤ ∑ q ∈ range k, |ent Bl i q| * entMax Q := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
          rw [abs_mul]; gcongr; exact ent_le_entMax _ _ _
      _ = (∑ q ∈ range k, |ent Bl i q|) * entMax Q := by rw [sum_mul]
      _ ≤ (rowSumMax Bl : ℤ) * entMax Q := by gcongr; exact rowsum_le Bl k hBlr i
      _ ≤ _ := by
          push_cast
          exact mul_le_mul (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_right (Nat.cast_nonneg _))
            (Nat.cast_nonneg _) (by positivity)
  have hBRb : ∀ i p, |BR i p| ≤ (((rowSumMax Bl + rowSumMax Br) * (entMax Q + entMax R) : ℕ) : ℤ) := by
    intro i p
    calc |BR i p| ≤ ∑ q ∈ range k, |ent Br i q| * entMax R := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
          rw [abs_mul]; gcongr; exact ent_le_entMax _ _ _
      _ = (∑ q ∈ range k, |ent Br i q|) * entMax R := by rw [sum_mul]
      _ ≤ (rowSumMax Br : ℤ) * entMax R := by gcongr; exact rowsum_le Br k hBrr i
      _ ≤ _ := by
          push_cast
          exact mul_le_mul (le_add_of_nonneg_left (Nat.cast_nonneg _)) (le_add_of_nonneg_left (Nat.cast_nonneg _))
            (Nat.cast_nonneg _) (by positivity)
  have hmQ : ∀ i, (mulTP k w Bl Q).getD i 0 = ∑ p ∈ range k, BQ i p * 2 ^ (w * p) :=
    mulTP_spec k w Bl Q hBlr hQl hQr
  have hmR : ∀ i, (mulTP k w Br R).getD i 0 = ∑ p ∈ range k, BR i p * 2 ^ (w * p) :=
    mulTP_spec k w Br R hBrr hRl hRr
  -- the k × k identity
  have hXtR : ∀ r ∈ (if τ then transp k X else X), r.length = k := by
    cases τ
    · simpa using hXr
    · intro r hr; simp only [if_true] at hr; rw [transp_row_length k X hXr r hr, hXl]
  have hXtL : (if τ then transp k X else X).length = k := by
    cases τ
    · simpa using hXl
    · simp [(transp_spec k X hXr).1]
  have hQtr : ∀ r ∈ transp k Q, r.length = k := fun r hr => by rw [transp_row_length k Q hQr r hr, hQl]
  have hRtr : ∀ r ∈ transp k R, r.length = k := fun r hr => by rw [transp_row_length k R hRr r hr, hRl]
  obtain ⟨-, yX⟩ := yRows_spec k w k (if τ then transp k X else X) (transp k Q) (transp k R) hXtL hXtR (transp_spec k R hRr).1 hRtr
  have hkk : ∀ i < k, ∀ j < k, ∑ p ∈ range k, ∑ q ∈ range k, ent Q p i * ent (if τ then transp k X else X) p q * ent R q j = al * ent X i j := by
    intro i hi
    have e := congrArg (fun l => l.getD i 0) hEX
    simp only at e
    rw [yX i hQtr, getD_map_zero (fun r => pk w (r.map (al * ·))) X [] (by rfl) i, pk_eq] at e
    have hlen : ((X.getD i []).map (al * ·)).length = k := by
      rw [List.length_map]; exact hXr _ (by rw [List.getD_eq_getElem _ [] (by rw [hXl]; exact hi)]; exact List.getElem_mem _)
    rw [hlen] at e
    have hd := digits_of_eq w k _ (fun j => ((X.getD i []).map (al * ·)).getD j 0)
      (rowSumMax (transp k Q) * entMax (if τ then transp k X else X) * rowSumMax (transp k R) + al.natAbs * entMax X)
      (rowSumMax (transp k Q) * entMax (if τ then transp k X else X) * rowSumMax (transp k R) + al.natAbs * entMax X)
      (fun j _ => by
        refine (Ymat_bound k (if τ then transp k X else X) (transp k Q) (transp k R) hQtr hRtr i j).trans ?_
        push_cast
        exact le_add_of_nonneg_right (by positivity))
      (fun j _ => by
        beta_reduce
        rw [getD_map_zero (al * ·) _ 0 (by simp) j]
        show |al * ent X i j| ≤ _
        rw [abs_mul, Int.abs_eq_natAbs al]
        push_cast
        refine le_add_of_nonneg_of_le (by positivity) ?_
        exact mul_le_mul_of_nonneg_left (ent_le_entMax X i j) (by positivity))
      hdX hdX e
    intro j hj
    have := hd j hj
    beta_reduce at this
    rw [getD_map_zero (al * ·) _ 0 (by simp) j] at this
    rw [show al * ent X i j = al * (X.getD i []).getD j 0 from rfl, ← this]
    refine sum_congr rfl fun p hp => sum_congr rfl fun q hq => ?_
    rw [ent_transp k Q hQr i p hi, ent_transp k R hRr j q hj]
  -- the folded matrix
  have hW : ∀ a' b', foldW k0 k1 k2 kq (ent (nth As 0 [])) (ent (nth As 1 [])) (ent (nth As 2 [])) (ent (nth As 3 []))
      (ent (nth Cs 0 [])) (ent (nth Cs 1 [])) (ent (nth Cs 2 [])) (ent (nth Cs 3 []))
      (fun c e => Ymat k X Bl Br (pidx k0 k1 k2 kq κ.1 c) (pidx k0 k1 k2 kq κ.1 e)) a' b' =
      ∑ p ∈ range k, ∑ q ∈ range k, LBf a' p * ent X p q * GBf b' q := by
    intro a' b'
    unfold foldW Ymat
    rw [alg1 (D4 k0 k1 k2 kq) _ _ (pidx k0 k1 k2 kq κ.1) k (ent Bl) (ent X) (ent Br)]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    rw [hLBf, hGBf]
    beta_reduce
    congr 1
    refine sum_congr rfl fun e he => ?_
    simp only [D4, mem_product, mem_range] at he
    rw [hCtE 0 (by norm_num) _ he.1, hCtE 1 (by norm_num) _ he.2.1, hCtE 2 (by norm_num) _ he.2.2.1,
      hCtE 3 (by norm_num) _ he.2.2.2]
  have hDLB : 4 * (n * (entMax (nth As 0 []) * entMax (nth As 1 []) * entMax (nth As 2 []) *
      entMax (nth As 3 [])) * (entMax Bl + entMax Br)) < 2 ^ w := hdL
  -- the two cases
  cases τ
  · simp only [Bool.false_eq_true, if_false] at hE1 hE2 hkk ⊢
    have dQ := digits_of_eq w k (LBf a) (BQ (enc4 k1 k2 kq a)) _ _ (fun p _ => hLBb a p) (fun p _ => hBQb _ p)
      hdL hdB (by rw [← hLB a ha, ← hmQ, hE1])
    have dR := digits_of_eq w k (GBf b) (BR (enc4 k1 k2 kq b)) _ _ (fun p _ => hGBb b p) (fun p _ => hBRb _ p)
      hdG hdB (by rw [← hGB b hb, ← hmR, hE2])
    rw [hW]
    rw [show ∑ p ∈ range k, ∑ q ∈ range k, LBf a p * ent X p q * GBf b q =
        ∑ p ∈ range k, ∑ q ∈ range k, BQ (enc4 k1 k2 kq a) p * ent X p q * BR (enc4 k1 k2 kq b) q from
      sum_congr rfl fun p hp => sum_congr rfl fun q hq => by
        rw [dQ p (mem_range.mp hp), dR q (mem_range.mp hq)]]
    simp only [hBQ, hBR]
    rw [alg2 k (ent Bl) (ent Br) (ent X) (ent Q) (ent R), Ymat, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [hkk p (mem_range.mp hp) q (mem_range.mp hq)]
    ring
  · simp only [if_true] at hE1 hE2 hkk ⊢
    have dQ := digits_of_eq w k (GBf a) (BQ (enc4 k1 k2 kq a)) _ _ (fun p _ => hGBb a p) (fun p _ => hBQb _ p)
      hdG hdB (by rw [← hGB a ha, ← hmQ, hE1])
    have dR := digits_of_eq w k (LBf b) (BR (enc4 k1 k2 kq b)) _ _ (fun p _ => hLBb b p) (fun p _ => hBRb _ p)
      hdL hdB (by rw [← hLB b hb, ← hmR, hE2])
    rw [hW]
    rw [show ∑ p ∈ range k, ∑ q ∈ range k, LBf b p * ent X p q * GBf a q =
        ∑ q ∈ range k, ∑ p ∈ range k, BQ (enc4 k1 k2 kq a) q * ent (transp k X) q p * BR (enc4 k1 k2 kq b) p by
      rw [sum_comm]
      exact sum_congr rfl fun q hq => sum_congr rfl fun p hp => by
        rw [dQ q (mem_range.mp hq), dR p (mem_range.mp hp), ent_transp k X hXr q p (mem_range.mp hq)]; ring]
    simp only [hBQ, hBR]
    rw [alg2 k (ent Bl) (ent Br) (ent (transp k X)) (ent Q) (ent R), Ymat, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [hkk p (mem_range.mp hp) q (mem_range.mp hq)]
    ring

/-! ## The fold lemma: `F ∘ κ = F` -/

theorem K3_eq_Fd (k0 k1 k2 kq : ℕ) (A0 A1 A2 A3 : ℕ → ℕ → ℤ) (G : ℕ → ℕ → ℕ → ℕ → ℤ) :
    K3 k0 k1 k2 A0 A1 A2 (fun a b => ∑ c ∈ range kq, ∑ e ∈ range kq, A3 c e * G a c b e) =
      Fd k0 k1 k2 kq A0 A1 A2 A3 (fun c e => G (enc3 k1 k2 c.1 c.2.1 c.2.2.1) c.2.2.2
        (enc3 k1 k2 e.1 e.2.1 e.2.2.1) e.2.2.2) := by
  unfold K3 Fd P4 sq
  rw [sum_product]
  refine sum_congr rfl fun x _ => ?_
  beta_reduce
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [cOf, eOf]
  ring

theorem nth_inv3_append (σ : List ℕ) (u : ℕ) (hu : u < 3) : nth (inv3 σ ++ [3]) u 0 = nth (inv3 σ) u 0 := by
  interval_cases u <;> rfl

/-- **The fold lemma.** If the table and `B`-level fold checks hold for `κ` (`foldBOK` checks `α = ∏_u α_u ≠ 0`), the part's
functional is invariant under `κ`: `F(κ · s) = F(s)` for all diagram tuples `s`. -/
theorem fold_invariant (w k0 k1 k2 kq k : ℕ) (rhos : List (List (List (List ℤ)))) (X Bl Br : List (List ℤ))
    (κ : KPar) (τ : Bool) (As Cs : List (List (List ℤ))) (als : List ℤ) (Q R : List (List ℤ))
    (htab : foldTabOK [k0, k1, k2, kq] rhos κ τ As Cs als = true)
    (hB : foldBOK w [k0, k1, k2, kq] k X Bl Br κ τ As Cs als Q R = true)
    (s0 s1 s2 s3 : ℕ) (hs0 : s0 < 24) (hs1 : s1 < 24) (hs2 : s2 < 24) (hs3 : s3 < 24) :
    Fv k0 k1 k2 kq rhos (Ymat k X Bl Br) (kact κ (nth [s0, s1, s2] (nth κ.1 0 0) 0))
        (kact κ (nth [s0, s1, s2] (nth κ.1 1 0) 0)) (kact κ (nth [s0, s1, s2] (nth κ.1 2 0) 0)) (kact κ s3) =
      Fv k0 k1 k2 kq rhos (Ymat k X Bl Br) s0 s1 s2 s3 := by
  obtain ⟨-, hσ, -, hT⟩ := foldTabOK_spec _ rhos κ τ As Cs als htab
  obtain ⟨hal0, h0, h1, h2, h3, -, hdim, hW⟩ := foldBOK_spec w k0 k1 k2 kq k X Bl Br κ τ As Cs als Q R hB
  set al := nth als 0 0 * nth als 1 0 * nth als 2 0 * nth als 3 0 with hal
  set σ := κ.1
  set Y := Ymat k X Bl Br
  set B : ℕ → ℕ → ℕ → ℤ := fun f => rhoE rhos f (kact κ (nth [s0, s1, s2] (nth σ f 0) 0)) with hBdef
  have hBc : ∀ c < 3, B (nth (inv3 σ) c 0) = rhoE rhos (nth (inv3 σ) c 0) (kact κ (nth [s0, s1, s2] c 0)) := by
    intro c hc; rw [hBdef]; dsimp only; rw [sigma_inv3 σ hσ c hc]
  -- the axis permutation
  have hperm := K3_perm k0 k1 k2 kq σ hσ B
    (fun a b => ∑ c ∈ range kq, ∑ e ∈ range kq, rhoE rhos 3 (kact κ s3) c e * Y (a * kq + c) (b * kq + e))
  rw [hdim 0 (by norm_num), hdim 1 (by norm_num), hdim 2 (by norm_num)] at hperm
  simp only [nth] at hperm
  have hL : Fv k0 k1 k2 kq rhos Y (kact κ (nth [s0, s1, s2] (nth σ 0 0) 0)) (kact κ (nth [s0, s1, s2] (nth σ 1 0) 0))
      (kact κ (nth [s0, s1, s2] (nth σ 2 0) 0)) (kact κ s3) =
      Fd k0 k1 k2 kq (B (nth (inv3 σ) 0 0)) (B (nth (inv3 σ) 1 0)) (B (nth (inv3 σ) 2 0))
        (rhoE rhos 3 (kact κ s3)) (fun c e => Y (pidx k0 k1 k2 kq σ c) (pidx k0 k1 k2 kq σ e)) := by
    unfold Fv
    rw [show rhoE rhos 0 (kact κ (nth [s0, s1, s2] (nth σ 0 0) 0)) = B 0 from rfl,
      show rhoE rhos 1 (kact κ (nth [s0, s1, s2] (nth σ 1 0) 0)) = B 1 from rfl,
      show rhoE rhos 2 (kact κ (nth [s0, s1, s2] (nth σ 2 0) 0)) = B 2 from rfl, ← hperm]
    exact K3_eq_Fd k0 k1 k2 kq _ _ _ _
      (fun a c b e => Y ((permIdx3 [k0, k1, k2, kq] σ).getD a 0 * kq + c) ((permIdx3 [k0, k1, k2, kq] σ).getD b 0 * kq + e))
  -- the fold identities
  have hfold : ∀ u < 4, ∀ s < 24, ∀ c < nth [k0, k1, k2, kq] u 1, ∀ e < nth [k0, k1, k2, kq] u 1,
      nth als u 0 * rhoE rhos (nth (inv3 σ ++ [3]) u 0) (kact κ s) c e =
        ∑ y ∈ sq (nth [k0, k1, k2, kq] u 1), ent (nth As u []) c y.1 * tflip τ (rhoE rhos u s) y.1 y.2 *
          ent (nth Cs u []) y.2 e := fun u hu s hs c hc e he => ((hT u hu).2 s hs c hc e he).symm
  have hscaled : al * Fd k0 k1 k2 kq (B (nth (inv3 σ) 0 0)) (B (nth (inv3 σ) 1 0)) (B (nth (inv3 σ) 2 0))
        (rhoE rhos 3 (kact κ s3)) (fun c e => Y (pidx k0 k1 k2 kq σ c) (pidx k0 k1 k2 kq σ e)) =
      Fd k0 k1 k2 kq
        (fun c e => ∑ y ∈ sq k0, ent (nth As 0 []) c y.1 * tflip τ (rhoE rhos 0 s0) y.1 y.2 * ent (nth Cs 0 []) y.2 e)
        (fun c e => ∑ y ∈ sq k1, ent (nth As 1 []) c y.1 * tflip τ (rhoE rhos 1 s1) y.1 y.2 * ent (nth Cs 1 []) y.2 e)
        (fun c e => ∑ y ∈ sq k2, ent (nth As 2 []) c y.1 * tflip τ (rhoE rhos 2 s2) y.1 y.2 * ent (nth Cs 2 []) y.2 e)
        (fun c e => ∑ y ∈ sq kq, ent (nth As 3 []) c y.1 * tflip τ (rhoE rhos 3 s3) y.1 y.2 * ent (nth Cs 3 []) y.2 e)
        (fun c e => Y (pidx k0 k1 k2 kq σ c) (pidx k0 k1 k2 kq σ e)) := by
    rw [hal, ← Fd_smul]
    refine Fd_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun c hc e he => ?_) (fun c hc e he => ?_) (fun c hc e he => ?_)
      (fun c hc e he => ?_) (fun _ _ _ _ => rfl)
    · rw [hBc 0 (by norm_num), ← nth_inv3_append σ 0 (by norm_num)]; exact hfold 0 (by norm_num) s0 hs0 c hc e he
    · rw [hBc 1 (by norm_num), ← nth_inv3_append σ 1 (by norm_num)]; exact hfold 1 (by norm_num) s1 hs1 c hc e he
    · rw [hBc 2 (by norm_num), ← nth_inv3_append σ 2 (by norm_num)]; exact hfold 2 (by norm_num) s2 hs2 c hc e he
    · exact hfold 3 (by norm_num) s3 hs3 c hc e he
  -- the folded matrix is `α Y`
  have hR : Fd k0 k1 k2 kq
        (fun c e => ∑ y ∈ sq k0, ent (nth As 0 []) c y.1 * tflip τ (rhoE rhos 0 s0) y.1 y.2 * ent (nth Cs 0 []) y.2 e)
        (fun c e => ∑ y ∈ sq k1, ent (nth As 1 []) c y.1 * tflip τ (rhoE rhos 1 s1) y.1 y.2 * ent (nth Cs 1 []) y.2 e)
        (fun c e => ∑ y ∈ sq k2, ent (nth As 2 []) c y.1 * tflip τ (rhoE rhos 2 s2) y.1 y.2 * ent (nth Cs 2 []) y.2 e)
        (fun c e => ∑ y ∈ sq kq, ent (nth As 3 []) c y.1 * tflip τ (rhoE rhos 3 s3) y.1 y.2 * ent (nth Cs 3 []) y.2 e)
        (fun c e => Y (pidx k0 k1 k2 kq σ c) (pidx k0 k1 k2 kq σ e)) =
      al * Fv k0 k1 k2 kq rhos Y s0 s1 s2 s3 := by
    rw [Fv_eq_Fd, ← Fd_Zsmul]
    cases τ
    · simp only [tflip, Bool.false_eq_true, if_false]
      rw [Fd_fold]
      refine Fd_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun a ha b hb => ?_)
      have := hW a ha b hb
      simp only [Bool.false_eq_true, if_false] at this
      rw [← this]; rfl
    · simp only [tflip, if_true]
      rw [Fd_foldT]
      refine Fd_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun a ha b hb => ?_)
      have := hW a ha b hb
      simp only [if_true] at this
      rw [← this]; rfl
  have := hscaled.trans hR
  rw [hL]
  exact mul_left_cancel₀ hal0 this

end LayerDProto

#print axioms LayerDProto.foldBOK_spec
#print axioms LayerDProto.fold_invariant
