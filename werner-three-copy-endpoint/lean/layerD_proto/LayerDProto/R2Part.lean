import LayerDProto.R2Sound
import LayerDProto.SymWerner

/-!
# Layer D, (E′): soundness of the per-part kernel `partD` (stage F)

The position codes (`posFull`, `posGrid`) and the packed permutation tables are proved to implement
the action `r_s(s) = g · ε(s) · g'` (`kact`) and its inverse (`kinv`), so the packed tables of
`tensorP3` put `ρ(r_s(t)) 2^(st·t)` (full coordinates) and `ρ(r_s(S1[i])) 2^(st·i)` (the grid coordinate)
at the right digits.
-/

open Finset

namespace LayerDProto

/-! ## The packed permutation tables -/

theorem pmul_eq : ∀ a b : Fin 24, pmul a b = mulTab a b := by decide
theorem pinv_eq : ∀ a : Fin 24, pinv a = invTab a := by decide

theorem peps_eq (ε : Bool) (s : Fin 24) : peps ε s = eIdx ε s := by
  cases ε <;> simp [peps, eIdx, pinv_eq]

/-- A parameter with `g, g' < 24`. -/
def KPar.ok (p : KPar) : Prop := p.2.2.1 < 24 ∧ p.2.2.2 < 24

theorem kact_eq (σ : List ℕ) (ε : Bool) (g g' s : Fin 24) :
    kact (σ, ε, g, g') s = mulTab (mulTab g (eIdx ε s)) g' := by
  simp only [kact, peps_eq, pmul_eq]

theorem kinv_eq (σ : List ℕ) (ε : Bool) (g g' m : Fin 24) :
    kinv (σ, ε, g, g') m = eIdx ε (mulTab (mulTab (invTab g) m) (invTab g')) := by
  simp only [kinv, pinv_eq, pmul_eq, peps_eq]

theorem kact_lt (p : KPar) (hp : p.ok) (s : ℕ) (hs : s < 24) : kact p s < 24 := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨hg, hg'⟩ := hp
  have := kact_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ ⟨s, hs⟩
  simp only at this
  rw [this]; exact Fin.isLt _

theorem kinv_lt (p : KPar) (hp : p.ok) (m : ℕ) (hm : m < 24) : kinv p m < 24 := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨hg, hg'⟩ := hp
  have := kinv_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ ⟨m, hm⟩
  simp only at this
  rw [this]; exact Fin.isLt _

theorem kinv_kact (p : KPar) (hp : p.ok) (s : ℕ) (hs : s < 24) : kinv p (kact p s) = s := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨hg, hg'⟩ := hp
  have h1 := kact_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ ⟨s, hs⟩
  simp only at h1
  rw [h1, kinv_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩]
  refine congrArg Fin.val (show _ = (⟨s, hs⟩ : Fin 24) from permTab_inj ?_)
  simp only [permTab_eIdx, permTab_mulTab, permTab_invTab, mul_assoc, mul_inv_cancel, mul_one,
    inv_mul_cancel_left]
  cases ε <;> simp [eInv]

theorem kact_kinv (p : KPar) (hp : p.ok) (m : ℕ) (hm : m < 24) : kact p (kinv p m) = m := by
  obtain ⟨σ, ε, g, g'⟩ := p
  obtain ⟨hg, hg'⟩ := hp
  have h1 := kinv_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩ ⟨m, hm⟩
  simp only at h1
  rw [h1, kact_eq σ ε ⟨g, hg⟩ ⟨g', hg'⟩]
  refine congrArg Fin.val (show _ = (⟨m, hm⟩ : Fin 24) from permTab_inj ?_)
  simp only [permTab_eIdx, permTab_mulTab, permTab_invTab]
  cases ε <;> simp [eInv, mul_assoc]

/-- Reindexing the 24 diagrams by `r_s`. -/
theorem sum_kact (p : KPar) (hp : p.ok) (h : ℕ → ℤ) :
    ∑ t ∈ range 24, h (kact p t) = ∑ m ∈ range 24, h m :=
  sum_nbij' (kact p) (kinv p) (fun a ha => mem_range.mpr (kact_lt p hp a (mem_range.mp ha)))
    (fun a ha => mem_range.mpr (kinv_lt p hp a (mem_range.mp ha)))
    (fun a ha => kinv_kact p hp a (mem_range.mp ha)) (fun a ha => kact_kinv p hp a (mem_range.mp ha))
    (fun _ _ => rfl)

/-! ## Position codes -/

theorem posFull_getD (p : KPar) (m : ℕ) (hm : m < 24) : (posFull p).getD m 0 = kinv p m + 1 := by
  simp [posFull, List.getD_eq_getElem?_getD, hm]

theorem posFull_length (p : KPar) : (posFull p).length = 24 := by simp [posFull]

theorem posGrid_getD (p : KPar) (g : List ℕ) (m : ℕ) (hm : m < 24) :
    (posGrid p g).getD m 0 = idxOf1 (kinv p m) g 0 := by
  simp [posGrid, List.getD_eq_getElem?_getD, hm]

theorem posGrid_length (p : KPar) (g : List ℕ) : (posGrid p g).length = 24 := by simp [posGrid]

theorem idxOf1_not_mem (x : ℕ) : ∀ (l : List ℕ) (i0 : ℕ), x ∉ l → idxOf1 x l i0 = 0
  | [], _, _ => rfl
  | y :: ys, i0, h => by
    have hy : x ≠ y := fun e => h (e ▸ List.mem_cons_self)
    have hys : x ∉ ys := fun e => h (List.mem_cons_of_mem _ e)
    simp [idxOf1, hy, idxOf1_not_mem x ys (i0 + 1) hys]

/-- The grid coordinate: `∑_t pcode (H t) (position of t in l) = ∑_i H(l[i]) 2^(st (i0 + i))`. -/
theorem grid_sum (st : ℕ) (H : ℕ → ℤ) : ∀ (l : List ℕ) (i0 : ℕ), l.Nodup → (∀ x ∈ l, x < 24) →
    ∑ t ∈ range 24, pcode st (H t) (idxOf1 t l i0) =
      ∑ i ∈ range l.length, H (l.getD i 0) * 2 ^ (st * (i0 + i))
  | [], _, _, _ => by simp [idxOf1, pcode]
  | x :: xs, i0, hnd, hlt => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih := grid_sum st H xs (i0 + 1) (List.nodup_cons.mp hnd).2
      (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
    have hpt : ∀ t, pcode st (H t) (idxOf1 t (x :: xs) i0) =
        (if t = x then H x * 2 ^ (st * i0) else 0) + pcode st (H t) (idxOf1 t xs (i0 + 1)) := by
      intro t
      by_cases htx : t = x
      · subst htx; simp [idxOf1, pcode, idxOf1_not_mem t xs _ hx]
      · simp [idxOf1, htx]
    simp only [hpt, sum_add_distrib, sum_ite_eq', mem_range, hlt x List.mem_cons_self, if_true, ih,
      List.length_cons, sum_range_succ', List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 2; ring

/-- A full coordinate: `∑_m pcode (h m) (posFull m) = ∑_t h(r_s t) 2^(st t)`. -/
theorem pcode_full_sum (p : KPar) (hp : p.ok) (st : ℕ) (h : ℕ → ℤ) :
    ∑ m ∈ range 24, pcode st (h m) ((posFull p).getD m 0) =
      ∑ t ∈ range 24, h (kact p t) * 2 ^ (st * t) := by
  rw [← sum_kact p hp]
  refine sum_congr rfl fun t ht => ?_
  rw [posFull_getD p _ (kact_lt p hp t (mem_range.mp ht)), kinv_kact p hp t (mem_range.mp ht)]
  simp [pcode]

/-- The grid coordinate: `∑_m pcode (h m) (posGrid m) = ∑_i h(r_s(S1[i])) 2^(st i)`. -/
theorem pcode_grid_sum (p : KPar) (hp : p.ok) (st : ℕ) (h : ℕ → ℤ) (S1 : List ℕ) (hnd : S1.Nodup)
    (hlt : ∀ x ∈ S1, x < 24) :
    ∑ m ∈ range 24, pcode st (h m) ((posGrid p S1).getD m 0) =
      ∑ i ∈ range S1.length, h (kact p (S1.getD i 0)) * 2 ^ (st * i) := by
  rw [← sum_kact p hp]
  have := grid_sum st (fun t => h (kact p t)) S1 0 hnd hlt
  simp only [zero_add] at this
  rw [← this]
  refine sum_congr rfl fun t ht => ?_
  rw [posGrid_getD p _ _ (kact_lt p hp t (mem_range.mp ht)), kinv_kact p hp t (mem_range.mp ht)]

theorem ptab_full (p : KPar) (hp : p.ok) (st : ℕ) (col : List ℤ) (hc : col.length = 24) :
    ptab st (posFull p) col = ∑ t ∈ range 24, col.getD (kact p t) 0 * 2 ^ (st * t) := by
  rw [ptab_spec st _ col (posFull_length p) hc]
  exact pcode_full_sum p hp st (fun m => col.getD m 0)

theorem ptab_grid (p : KPar) (hp : p.ok) (st : ℕ) (col : List ℤ) (hc : col.length = 24)
    (S1 : List ℕ) (hnd : S1.Nodup) (hlt : ∀ x ∈ S1, x < 24) :
    ptab st (posGrid p S1) col = ∑ i ∈ range S1.length, col.getD (kact p (S1.getD i 0)) 0 * 2 ^ (st * i) := by
  rw [ptab_spec st _ col (posGrid_length p S1) hc]
  exact pcode_grid_sum p hp st (fun m => col.getD m 0) S1 hnd hlt

/-! ## Three-axis contractions in box form -/

/-- The Kronecker index `(a₀ k₁ + a₁) k₂ + a₂`. -/
def enc3 (k1 k2 a0 a1 a2 : ℕ) : ℕ := (a0 * k1 + a1) * k2 + a2

theorem enc3_lt {k0 k1 k2 a0 a1 a2 : ℕ} (h0 : a0 < k0) (h1 : a1 < k1) (h2 : a2 < k2) :
    enc3 k1 k2 a0 a1 a2 < k0 * k1 * k2 := by
  unfold enc3
  have e1 : a0 * k1 + a1 < k0 * k1 := by nlinarith
  have e2 : a0 * k1 + a1 + 1 ≤ k0 * k1 := e1
  nlinarith

theorem enc3_digits {k1 k2 a0 a1 a2 : ℕ} (h1 : a1 < k1) (h2 : a2 < k2) :
    enc3 k1 k2 a0 a1 a2 / (k1 * k2) = a0 ∧ enc3 k1 k2 a0 a1 a2 / k2 % k1 = a1 ∧
      enc3 k1 k2 a0 a1 a2 % k2 = a2 := by
  have hk2 : 0 < k2 := by omega
  have hk1 : 0 < k1 := by omega
  have hd : enc3 k1 k2 a0 a1 a2 / k2 = a0 * k1 + a1 := by
    unfold enc3
    rw [add_comm, Nat.add_mul_div_right _ _ hk2, Nat.div_eq_of_lt h2, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_comm k1 k2, ← Nat.div_div_eq_div_mul, hd, add_comm, Nat.add_mul_div_right _ _ hk1,
      Nat.div_eq_of_lt h1, zero_add]
  · rw [hd, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  · unfold enc3
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]

/-- `k₀ × k₁ × k₂` index pairs `((c₀, e₀), (c₁, e₁), (c₂, e₂))`. -/
def box (k0 k1 k2 : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  (range k0 ×ˢ range k0) ×ˢ ((range k1 ×ˢ range k1) ×ˢ (range k2 ×ˢ range k2))

/-- `∑ A₀[c₀][e₀] A₁[c₁][e₁] A₂[c₂][e₂] L[(c₀,c₁,c₂)][(e₀,e₁,e₂)]`. -/
def K3 (k0 k1 k2 : ℕ) (A0 A1 A2 L : ℕ → ℕ → ℤ) : ℤ :=
  ∑ x ∈ box k0 k1 k2, A0 x.1.1 x.1.2 * A1 x.2.1.1 x.2.1.2 * A2 x.2.2.1 x.2.2.2 *
    L (enc3 k1 k2 x.1.1 x.2.1.1 x.2.2.1) (enc3 k1 k2 x.1.2 x.2.1.2 x.2.2.2)

theorem K3_nested (k0 k1 k2 : ℕ) (A0 A1 A2 L : ℕ → ℕ → ℤ) :
    K3 k0 k1 k2 A0 A1 A2 L = ∑ c0 ∈ range k0, ∑ e0 ∈ range k0, A0 c0 e0 *
      ∑ c1 ∈ range k1, ∑ e1 ∈ range k1, A1 c1 e1 * ∑ c2 ∈ range k2, ∑ e2 ∈ range k2, A2 c2 e2 *
        L ((c0 * k1 + c1) * k2 + c2) ((e0 * k1 + e1) * k2 + e2) := by
  simp only [K3, box, sum_product, mul_sum, enc3, mul_assoc]

theorem K3_congr (k0 k1 k2 : ℕ) (A0 A1 A2 L A0' A1' A2' L' : ℕ → ℕ → ℤ)
    (h0 : ∀ c < k0, ∀ e < k0, A0 c e = A0' c e) (h1 : ∀ c < k1, ∀ e < k1, A1 c e = A1' c e)
    (h2 : ∀ c < k2, ∀ e < k2, A2 c e = A2' c e)
    (hL : ∀ a < k0 * k1 * k2, ∀ b < k0 * k1 * k2, L a b = L' a b) :
    K3 k0 k1 k2 A0 A1 A2 L = K3 k0 k1 k2 A0' A1' A2' L' := by
  refine sum_congr rfl fun x hx => ?_
  simp only [box, mem_product, mem_range] at hx
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, e, f⟩ := hx
  rw [h0 _ a _ b, h1 _ c _ d, h2 _ e _ f, hL _ (enc3_lt a c e) _ (enc3_lt b d f)]

theorem K3_sum0 (k0 k1 k2 : ℕ) {ι : Type*} (s : Finset ι) (B : ι → ℕ → ℕ → ℤ) (W : ι → ℤ)
    (A1 A2 L : ℕ → ℕ → ℤ) :
    K3 k0 k1 k2 (fun c e => ∑ t ∈ s, B t c e * W t) A1 A2 L = ∑ t ∈ s, K3 k0 k1 k2 (B t) A1 A2 L * W t := by
  simp only [K3, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem K3_sum1 (k0 k1 k2 : ℕ) {ι : Type*} (s : Finset ι) (B : ι → ℕ → ℕ → ℤ) (W : ι → ℤ)
    (A0 A2 L : ℕ → ℕ → ℤ) :
    K3 k0 k1 k2 A0 (fun c e => ∑ t ∈ s, B t c e * W t) A2 L = ∑ t ∈ s, K3 k0 k1 k2 A0 (B t) A2 L * W t := by
  simp only [K3, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem K3_sum2 (k0 k1 k2 : ℕ) {ι : Type*} (s : Finset ι) (B : ι → ℕ → ℕ → ℤ) (W : ι → ℤ)
    (A0 A1 L : ℕ → ℕ → ℤ) :
    K3 k0 k1 k2 A0 A1 (fun c e => ∑ t ∈ s, B t c e * W t) L = ∑ t ∈ s, K3 k0 k1 k2 A0 A1 (B t) L * W t := by
  simp only [K3, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-! ## The axis permutation -/

theorem inv3_012 : inv3 [0, 1, 2] = [0, 1, 2] := rfl
theorem inv3_021 : inv3 [0, 2, 1] = [0, 2, 1] := rfl
theorem inv3_102 : inv3 [1, 0, 2] = [1, 0, 2] := rfl
theorem inv3_120 : inv3 [1, 2, 0] = [2, 0, 1] := rfl
theorem inv3_201 : inv3 [2, 0, 1] = [1, 2, 0] := rfl
theorem inv3_210 : inv3 [2, 1, 0] = [2, 1, 0] := rfl

/-- Axis `c` of an index-pair triple. -/
def ax (x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) (c : ℕ) : ℕ × ℕ := nth [x.1, x.2.1, x.2.2] c (0, 0)

/-- New axes to old axes: old axis `f` is new axis `σ f`. -/
def toOld (σ : List ℕ) (x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  (ax x (nth σ 0 0), ax x (nth σ 1 0), ax x (nth σ 2 0))

/-- Old axes to new axes: new axis `c` is old axis `σ⁻¹ c`. -/
def toNew (σ : List ℕ) (y : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  let fc := inv3 σ
  (ax y (nth fc 0 0), ax y (nth fc 1 0), ax y (nth fc 2 0))

theorem permIdx3_getD (k0 k1 k2 kq : ℕ) (σ : List ℕ) (a0 a1 a2 : ℕ)
    (h0 : a0 < nth [k0, k1, k2, kq] (nth (inv3 σ) 0 0) 1) (h1 : a1 < nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1)
    (h2 : a2 < nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1) :
    (permIdx3 [k0, k1, k2, kq] σ).getD (enc3 (nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1)
        (nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1) a0 a1 a2) 0 =
      enc3 k1 k2 (nth [a0, a1, a2] (nth σ 0 0) 0) (nth [a0, a1, a2] (nth σ 1 0) 0)
        (nth [a0, a1, a2] (nth σ 2 0) 0) := by
  have hlt := enc3_lt h0 h1 h2
  obtain ⟨d0, d1, d2⟩ := enc3_digits (a0 := a0) h1 h2
  simp only [permIdx3, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some]
  rw [d0, d1, d2]
  rfl

/-- **Permuting the axes.** Contracting the axis-permuted matrix against the tables in the new order
is the contraction of the original matrix in the old order. -/
theorem K3_perm (k0 k1 k2 kq : ℕ) (σ : List ℕ) (hσ : σ ∈ perms3) (B : ℕ → ℕ → ℕ → ℤ)
    (L : ℕ → ℕ → ℤ) :
    K3 (nth [k0, k1, k2, kq] (nth (inv3 σ) 0 0) 1) (nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1)
        (nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1)
        (B (nth (inv3 σ) 0 0)) (B (nth (inv3 σ) 1 0)) (B (nth (inv3 σ) 2 0))
        (fun a b => L ((permIdx3 [k0, k1, k2, kq] σ).getD a 0) ((permIdx3 [k0, k1, k2, kq] σ).getD b 0)) =
      K3 k0 k1 k2 (B 0) (B 1) (B 2) L := by
  unfold K3
  refine sum_nbij' (toOld σ) (toNew σ) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [box, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio,
      mem_coe] at hx ⊢
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [toOld, ax, nth, inv3, idxOf1] at hx ⊢ <;> simp at hx ⊢ <;> tauto
  · intro x hx
    simp only [box, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio,
      mem_coe] at hx ⊢
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [toNew, ax, nth, inv3, idxOf1] at hx ⊢ <;> simp at hx ⊢ <;> tauto
  · intro x _
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro x _
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro x hx
    simp only [box, mem_product, mem_range] at hx
    obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, a2, b2⟩ := hx
    beta_reduce
    rw [permIdx3_getD k0 k1 k2 kq σ _ _ _ a0 a1 a2, permIdx3_getD k0 k1 k2 kq σ _ _ _ b0 b1 b2]
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [toOld, ax, nth, inv3_012, inv3_021, inv3_102, inv3_120, inv3_201, inv3_210] <;> ring

theorem permIdx3_props (k0 k1 k2 kq : ℕ) (σ : List ℕ) (hσ : σ ∈ perms3) :
    (permIdx3 [k0, k1, k2, kq] σ).length = k0 * k1 * k2 ∧
      ∀ i ∈ permIdx3 [k0, k1, k2, kq] σ, i < k0 * k1 * k2 := by
  have hdig : ∀ a b c i : ℕ, i < a * b * c → i / (b * c) < a ∧ i / c % b < b ∧ i % c < c := by
    intro a b c i hi
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hi
      · exact h
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hi
      · exact h
    refine ⟨?_, Nat.mod_lt _ hb, Nat.mod_lt _ hc⟩
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc i < a * b * c := hi
      _ = a * (b * c) := by ring
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [permIdx3, inv3_012, inv3_021, inv3_102, inv3_120, inv3_201, inv3_210, nth,
      List.length_map, List.length_range, List.mem_map, List.mem_range] <;>
    (first | refine ⟨by ring, ?_⟩ | refine ⟨trivial, ?_⟩) <;> rintro _ ⟨i, hi, rfl⟩ <;> obtain ⟨d0, d1, d2⟩ := hdig _ _ _ i hi
  · exact enc3_lt d0 d1 d2
  · exact enc3_lt d0 d2 d1
  · exact enc3_lt d1 d0 d2
  · exact enc3_lt d1 d2 d0
  · exact enc3_lt d2 d0 d1
  · exact enc3_lt d2 d1 d0

theorem sigma_inv3 (σ : List ℕ) (hσ : σ ∈ perms3) :
    ∀ c < 3, nth σ (nth (inv3 σ) c 0) 0 = c := by
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## One coset representative -/

/-- **The packed tables of one representative.** -/
theorem tensorP3_rep (β s1 k0 k1 k2 : ℕ) (h0 : 0 < k0) (h1 : 0 < k1) (h2 : 0 < k2) (p : KPar) (hp : p.ok)
    (S1 : List ℕ) (hnd : S1.Nodup) (hlt : ∀ x ∈ S1, x < 24)
    (R0 R1 R2 : List (List (List ℤ))) (hR0 : R0.length = 24) (hR1 : R1.length = 24) (hR2 : R2.length = 24)
    (hR0m : ∀ M ∈ R0, M.length = k0 ∧ ∀ r ∈ M, r.length = k0)
    (hR1m : ∀ M ∈ R1, M.length = k1 ∧ ∀ r ∈ M, r.length = k1)
    (hR2m : ∀ M ∈ R2, M.length = k2 ∧ ∀ r ∈ M, r.length = k2)
    (L : List (List ℤ)) (hL : L.length = k0 * k1 * k2) (hLr : ∀ r ∈ L, r.length = k0 * k1 * k2) :
    tensorP3 β s1 [k0, k1, k2] R0 [cols k1 R1, cols k2 R2] [posFull p, posFull p, posGrid p S1] L =
      ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
        K3 k0 k1 k2 (ent (R0.getD (kact p t0) [])) (ent (R1.getD (kact p t1) []))
          (ent (R2.getD (kact p (S1.getD i2 0)) [])) (ent L) * 2 ^ (β * (i2 + s1 * (t1 + 24 * t0))) := by
  obtain ⟨c1l, c1r, c1e⟩ := cols_spec k1 R1 hR1 hR1m
  obtain ⟨c2l, c2r, c2e⟩ := cols_spec k2 R2 hR2 hR2m
  rw [tensorP3_spec β s1 k0 k1 k2 h0 h1 h2 R0 hR0 hR0m _ _ c1l c2l _ _ _ (posFull_length p) L hL hLr]
  have e1 := pcode_full_sum p hp (β * 24 * s1) (fun m => K3 k0 k1 k2 (ent (R0.getD m []))
    (fun c e => ptab (β * s1) (posFull p) ((cols k1 R1).getD (c * k1 + e) []))
    (fun c e => ptab β (posGrid p S1) ((cols k2 R2).getD (c * k2 + e) [])) (ent L))
  simp only [K3_nested] at e1
  rw [e1]
  refine sum_congr rfl fun t0 _ => ?_
  have hcol : ∀ k (cs : List (List ℤ)), cs.length = k * k → (∀ r ∈ cs, r.length = 24) →
      ∀ c < k, ∀ e < k, (cs.getD (c * k + e) []).length = 24 := by
    intro k cs hl hr c hc e he
    have : c * k + e < cs.length := by rw [hl]; nlinarith
    rw [List.getD_eq_getElem _ [] this]; exact hr _ (List.getElem_mem _)
  rw [← K3_nested, K3_congr k0 k1 k2 _ _ _ _ (ent (R0.getD (kact p t0) []))
    (fun c e => ∑ t1 ∈ range 24, ent (R1.getD (kact p t1) []) c e * 2 ^ (β * s1 * t1))
    (fun c e => ∑ i2 ∈ range S1.length, ent (R2.getD (kact p (S1.getD i2 0)) []) c e * 2 ^ (β * i2))
    (ent L) (fun _ _ _ _ => rfl) ?_ ?_ (fun _ _ _ _ => rfl)]
  · rw [K3_sum1, sum_mul]
    refine sum_congr rfl fun t1 _ => ?_
    rw [K3_sum2, sum_mul, sum_mul]
    refine sum_congr rfl fun i2 _ => ?_
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    ring
  · intro c hc e he
    rw [ptab_full p hp _ _ (hcol k1 _ c1l c1r c hc e he)]
    exact sum_congr rfl fun t _ => by rw [c1e c hc e he]
  · intro c hc e he
    rw [ptab_grid p hp _ _ (hcol k2 _ c2l c2r c hc e he) S1 hnd hlt]
    exact sum_congr rfl fun t _ => by rw [c2e c hc e he]

/-- `ρ_f(s)[a][b]` read from the module data. -/
def rhoE (rhos : List (List (List (List ℤ)))) (f s : ℕ) : ℕ → ℕ → ℤ := ent ((rhos.getD f []).getD s [])

theorem kn_props (k0 k1 k2 kq : ℕ) (hk0 : 0 < k0) (hk1 : 0 < k1) (hk2 : 0 < k2) (σ : List ℕ)
    (hσ : σ ∈ perms3) :
    nth [k0, k1, k2, kq] (nth (inv3 σ) 0 0) 1 * nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1 *
        nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1 = k0 * k1 * k2 ∧
      0 < nth [k0, k1, k2, kq] (nth (inv3 σ) 0 0) 1 ∧ 0 < nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1 ∧
      0 < nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1 ∧
      nth (inv3 σ) 0 0 < 3 ∧ nth (inv3 σ) 1 0 < 3 ∧ nth (inv3 σ) 2 0 < 3 := by
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [inv3_012, inv3_021, inv3_102, inv3_120, inv3_201, inv3_210, nth] <;>
    first | assumption | ring1 | norm_num

/-- **One coset representative, in the original axis order.** -/
theorem sgroup_rep (β s1 k0 k1 k2 kq : ℕ) (hk0 : 0 < k0) (hk1 : 0 < k1) (hk2 : 0 < k2)
    (σ : List ℕ) (hσ : σ ∈ perms3) (p : KPar) (hp : p.ok)
    (S1 : List ℕ) (hnd : S1.Nodup) (hlt : ∀ x ∈ S1, x < 24) (rhos : List (List (List (List ℤ))))
    (hrho : ∀ f < 3, (rhos.getD f []).length = 24 ∧ ∀ M ∈ rhos.getD f [],
      M.length = nth [k0, k1, k2, kq] f 1 ∧ ∀ r ∈ M, r.length = nth [k0, k1, k2, kq] f 1)
    (L : List (List ℤ)) (hL : L.length = k0 * k1 * k2) (hLr : ∀ r ∈ L, r.length = k0 * k1 * k2)
    (Lf : ℕ → ℕ → ℤ) (hLf : ∀ a < k0 * k1 * k2, ∀ b < k0 * k1 * k2, ent L a b = Lf a b) :
    tensorP3 β s1 [nth [k0, k1, k2, kq] (nth (inv3 σ) 0 0) 1, nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1,
        nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1] (nth rhos (nth (inv3 σ) 0 0) [])
      [cols (nth [k0, k1, k2, kq] (nth (inv3 σ) 1 0) 1) (nth rhos (nth (inv3 σ) 1 0) []),
        cols (nth [k0, k1, k2, kq] (nth (inv3 σ) 2 0) 1) (nth rhos (nth (inv3 σ) 2 0) [])]
      [posFull p, posFull p, posGrid p S1] (permY (k0 * k1 * k2) (permIdx3 [k0, k1, k2, kq] σ) L) =
    ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
      K3 k0 k1 k2 (rhoE rhos 0 (kact p (nth [t0, t1, S1.getD i2 0] (nth σ 0 0) 0)))
        (rhoE rhos 1 (kact p (nth [t0, t1, S1.getD i2 0] (nth σ 1 0) 0)))
        (rhoE rhos 2 (kact p (nth [t0, t1, S1.getD i2 0] (nth σ 2 0) 0))) Lf *
        2 ^ (β * (i2 + s1 * (t1 + 24 * t0))) := by
  obtain ⟨hkn, hn0, hn1, hn2, hf0, hf1, hf2⟩ := kn_props k0 k1 k2 kq hk0 hk1 hk2 σ hσ
  obtain ⟨il, ib⟩ := permIdx3_props k0 k1 k2 kq σ hσ
  obtain ⟨yl, yr, ye⟩ := permY_spec (k0 * k1 * k2) _ L il hL hLr ib
  have hR : ∀ c, c < 3 → (nth rhos c []).length = 24 ∧ ∀ M ∈ nth rhos c [],
      M.length = nth [k0, k1, k2, kq] c 1 ∧ ∀ r ∈ M, r.length = nth [k0, k1, k2, kq] c 1 := by
    intro c hc; rw [nth_eq_getD]; exact hrho c hc
  rw [tensorP3_rep β s1 _ _ _ hn0 hn1 hn2 p hp S1 hnd hlt _ _ _ (hR _ hf0).1 (hR _ hf1).1 (hR _ hf2).1
    (hR _ hf0).2 (hR _ hf1).2 (hR _ hf2).2 _ (by rw [yl, hkn]) (fun r hr => by rw [yr r hr, hkn])]
  refine sum_congr rfl fun t0 _ => sum_congr rfl fun t1 _ => sum_congr rfl fun i2 _ => ?_
  congr 1
  set B : ℕ → ℕ → ℕ → ℤ := fun f => rhoE rhos f (kact p (nth [t0, t1, S1.getD i2 0] (nth σ f 0) 0)) with hB
  have hBc : ∀ c < 3, B (nth (inv3 σ) c 0) = rhoE rhos (nth (inv3 σ) c 0) (kact p (nth [t0, t1, S1.getD i2 0] c 0)) := by
    intro c hc; rw [hB]; dsimp only; rw [sigma_inv3 σ hσ c hc]
  rw [K3_congr _ _ _ _ _ _ _ (B (nth (inv3 σ) 0 0)) (B (nth (inv3 σ) 1 0)) (B (nth (inv3 σ) 2 0))
    (fun a b => Lf ((permIdx3 [k0, k1, k2, kq] σ).getD a 0) ((permIdx3 [k0, k1, k2, kq] σ).getD b 0))
    ?_ ?_ ?_ ?_, K3_perm k0 k1 k2 kq σ hσ B Lf]
  · intro c _ e _; rw [hBc 0 (by norm_num)]; simp only [rhoE, nth, nth_eq_getD]
  · intro c _ e _; rw [hBc 1 (by norm_num)]; simp only [rhoE, nth, nth_eq_getD]
  · intro c _ e _; rw [hBc 2 (by norm_num)]; simp only [rhoE, nth, nth_eq_getD]
  · intro a ha b hb
    rw [hkn] at ha hb
    rw [ye a ha b hb]
    have hm : ∀ x < k0 * k1 * k2, (permIdx3 [k0, k1, k2, kq] σ).getD x 0 < k0 * k1 * k2 := by
      intro x hx
      rw [List.getD_eq_getElem _ 0 (il ▸ hx)]
      exact ib _ (List.getElem_mem _)
    exact hLf _ (hm a ha) _ (hm b hb)

/-! ## The checks of `partD` -/

theorem foldl_add_sum (l : List ℤ) (a : ℤ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

theorem mapM_sum {α : Type} (f : α → Option ℤ) (g : α → ℤ) : ∀ (l : List α) (vs : List ℤ),
    (∀ a ∈ l, ∀ x, f a = some x → x = g a) → l.mapM f = some vs → vs.sum = (l.map g).sum
  | [], vs, _, h => by simp at h; subst h; rfl
  | x :: xs, vs, hfg, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rw [List.sum_cons, List.map_cons, List.sum_cons, hfg x List.mem_cons_self b hx,
          mapM_sum f g xs bs (fun a ha => hfg a (List.mem_cons_of_mem _ ha)) hxs]

theorem le_maxNat : ∀ (l : List ℕ), ∀ x ∈ l, x ≤ maxNat l
  | [], x, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_maxNat ys x h) (le_max_right _ _)

theorem ent_le_entMax (M : List (List ℤ)) (i j : ℕ) : |ent M i j| ≤ (entMax M : ℤ) := by
  unfold ent
  by_cases hi : i < M.length
  · rw [List.getD_eq_getElem _ [] hi]
    by_cases hj : j < M[i].length
    · rw [List.getD_eq_getElem _ 0 hj]
      have h1 : M[i][j].natAbs ≤ maxNat (M[i].map Int.natAbs) :=
        le_maxNat _ _ (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
      have h2 : maxNat (M[i].map Int.natAbs) ≤ entMax M :=
        le_maxNat _ _ (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)
      rw [Int.abs_eq_natAbs]; exact_mod_cast h1.trans h2
    · rw [List.getD_eq_default _ _ (not_lt.mp hj)]; simp
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]; simp

theorem rowsum_le (M : List (List ℤ)) (k : ℕ) (hM : ∀ r ∈ M, r.length = k) (i : ℕ) :
    ∑ p ∈ range k, |ent M i p| ≤ (rowSumMax M : ℤ) := by
  by_cases hi : i < M.length
  · have hr := hM _ (List.getElem_mem hi)
    have e : ∑ p ∈ range k, |ent M i p| = (sumAbs M[i] : ℤ) := by
      rw [sumAbs_eq, hr]
      exact sum_congr rfl fun p _ => by rw [ent, List.getD_eq_getElem _ [] hi]
    rw [e]; exact_mod_cast le_maxNat _ _ (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)
  · have : ∀ p, ent M i p = 0 := fun p => by
      rw [ent, List.getD_eq_default _ _ (not_lt.mp hi)]; simp
    simp [this]

/-- `Y = B_l X B_rᵀ`. -/
def Ymat (k : ℕ) (X Bl Br : List (List ℤ)) (i j : ℕ) : ℤ :=
  ∑ p ∈ range k, ∑ q ∈ range k, ent Bl i p * ent X p q * ent Br j q

theorem Ymat_bound (k : ℕ) (X Bl Br : List (List ℤ)) (hBl : ∀ r ∈ Bl, r.length = k)
    (hBr : ∀ r ∈ Br, r.length = k) (i j : ℕ) :
    |Ymat k X Bl Br i j| ≤ (rowSumMax Bl : ℤ) * entMax X * rowSumMax Br := by
  unfold Ymat
  have hX : (0 : ℤ) ≤ entMax X := Nat.cast_nonneg _
  calc |∑ p ∈ range k, ∑ q ∈ range k, ent Bl i p * ent X p q * ent Br j q|
      ≤ ∑ p ∈ range k, ∑ q ∈ range k, |ent Bl i p| * entMax X * |ent Br j q| := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
        rw [abs_mul, abs_mul]
        gcongr
        exact ent_le_entMax X p q
    _ = (∑ p ∈ range k, |ent Bl i p|) * entMax X * ∑ q ∈ range k, |ent Br j q| := by
        rw [sum_mul, sum_mul]
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum]
    _ ≤ (rowSumMax Bl : ℤ) * entMax X * rowSumMax Br := by
        have h1 := rowsum_le Bl k hBl i
        have h2 := rowsum_le Br k hBr j
        have h3 : (0 : ℤ) ≤ ∑ q ∈ range k, |ent Br j q| := sum_nonneg fun _ _ => abs_nonneg _
        gcongr

theorem isRect_spec (r c : ℕ) (M : List (List ℤ)) (h : isRect r c M = true) :
    M.length = r ∧ ∀ row ∈ M, row.length = c := by
  simp only [isRect, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem rhosOK_spec (ks : List ℕ) (rhos : List (List (List (List ℤ)))) (h : rhosOK ks rhos = true) :
    ∀ f < 4, (rhos.getD f []).length = 24 ∧
      ∀ M ∈ rhos.getD f [], M.length = nth ks f 1 ∧ ∀ r ∈ M, r.length = nth ks f 1 := by
  intro f hf
  simp only [rhosOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h.2 f hf
  rw [← nth_eq_getD]
  exact ⟨h1, fun M hM => isRect_spec _ _ M (h2 M hM)⟩

theorem groupOK_spec (d : ℕ) (gs : List MGroup) (h : groupOK d gs = true) :
    ∀ mg ∈ gs, ∀ sg ∈ mg.2, ∀ p ∈ sg.2, p.1 = sg.1 ∧ kact p d = mg.1 := by
  simp only [groupOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- What `partOK` guarantees. -/
theorem partOK_spec (w bnd : ℕ) (ks : List ℕ) (k : ℕ) (X Bl Br : List (List ℤ))
    (rhos : List (List (List (List ℤ)))) (d : ℕ) (S1 : List ℕ) (gs : List MGroup)
    (h : partOK w bnd ks k X Bl Br rhos d S1 gs = true) :
    ∃ k0 k1 k2 kq, ks = [k0, k1, k2, kq] ∧ 0 < k0 ∧ 0 < k1 ∧ 0 < k2 ∧ 0 < kq ∧ 0 < w ∧
      rhosOK ks rhos = true ∧ isRect k k X = true ∧ isRect (k0 * k1 * k2 * kq) k Bl = true ∧
      isRect (k0 * k1 * k2 * kq) k Br = true ∧ S1.Nodup ∧ (∀ x ∈ S1, x < 24) ∧ d < 24 ∧
      (∀ mg ∈ gs, mg.1 < 24 ∧ ∀ sg ∈ mg.2, sg.1 ∈ perms3 ∧ ∀ p ∈ sg.2, KPar.ok p) ∧
      4 * (kq * kq * maxNat ((nth rhos 3 []).map entMax) * (rowSumMax Bl * entMax X * rowSumMax Br) + 1)
        ≤ 2 ^ w ∧ 4 * bnd < 2 ^ (kq * w) := by
  unfold partOK at h
  split at h
  · rename_i k0 k1 k2 kq
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem, and_assoc] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    exact ⟨k0, k1, k2, kq, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      fun mg hmg => ⟨(h13 mg hmg).1, fun sg hsg => ⟨((h13 mg hmg).2 sg hsg).1,
        fun p hp => ((h13 mg hmg).2 sg hsg).2 p hp⟩⟩, h14, h15⟩
  · simp at h

/-! ## Soundness of `partD` -/

/-- The value `F(t) = ⟨Y, ρ₀(s₀) ⊗ ρ₁(s₁) ⊗ ρ₂(s₂) ⊗ ρ_q(s_q)⟩` of a part at the diagrams `s`
(Kronecker order: coordinate 0, 1, 2, qubit). -/
def Fv (k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ) (s0 s1 s2 sq : ℕ) : ℤ :=
  K3 k0 k1 k2 (rhoE rhos 0 s0) (rhoE rhos 1 s1) (rhoE rhos 2 s2)
    (fun a b => ∑ c ∈ range kq, ∑ e ∈ range kq, rhoE rhos 3 sq c e * Y (a * kq + c) (b * kq + e))

/-- The packed grid values of one representative `p`: `∑_{t₀, t₁, i₂} F(p · (t₀, t₁, S1[i₂], d)) 2^(β pos)`
with `(p · t)_f = r_s(t_{σ f})`, `(p · t)_q = r_s(d)`. -/
def repVal (β k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ) (S1 : List ℕ)
    (d : ℕ) (p : KPar) : ℤ :=
  ∑ t0 ∈ range 24, ∑ t1 ∈ range 24, ∑ i2 ∈ range S1.length,
    Fv k0 k1 k2 kq rhos Y (kact p (nth [t0, t1, S1.getD i2 0] (nth p.1 0 0) 0))
      (kact p (nth [t0, t1, S1.getD i2 0] (nth p.1 1 0) 0))
      (kact p (nth [t0, t1, S1.getD i2 0] (nth p.1 2 0) 0)) (kact p d) *
      2 ^ (β * (i2 + S1.length * (t1 + 24 * t0)))

/-- **Soundness of the checked per-part kernel.** If `partD` returns `v`, then `v` is `fac` times the sum,
over the listed representatives `p`, of the packed grid values of `F ∘ p`, with `F` the part's
functional for `Y = B_l X B_rᵀ`. -/
theorem partD_sound (β w bnd : ℕ) (ks : List ℕ) (k : ℕ) (X Bl Br : List (List ℤ)) (fac : ℤ)
    (rhos : List (List (List (List ℤ)))) (d : ℕ) (S1 : List ℕ) (gs : List MGroup) (v : ℤ)
    (h : partD β w bnd ks k X Bl Br fac rhos d S1 gs = some v) :
    ∃ k0 k1 k2 kq, ks = [k0, k1, k2, kq] ∧
      (∀ mg ∈ gs, ∀ sg ∈ mg.2, ∀ p ∈ sg.2, KPar.ok p ∧ p.1 ∈ perms3) ∧
      v = fac * (gs.map fun mg => (mg.2.map fun sg =>
        (sg.2.map (repVal β k0 k1 k2 kq rhos (Ymat k X Bl Br) S1 d)).sum).sum).sum := by
  unfold partD at h
  split at h
  · exact absurd h (by simp)
  rename_i hb
  have hb' : (groupOK d gs && partOK w bnd ks k X Bl Br rhos d S1 gs) = true := by simpa using hb
  rw [Bool.and_eq_true] at hb'
  obtain ⟨hg, hpo⟩ := hb'
  have hgs := groupOK_spec d gs hg
  obtain ⟨k0, k1, k2, kq, rfl, hk0, hk1, hk2, hkq, hw, hrh, hX, hBl, hBr, hnd, hlt, hd, hmg, hwb, hbnd⟩ :=
    partOK_spec w bnd ks k X Bl Br rhos d S1 gs hpo
  have hrho := rhosOK_spec _ rhos hrh
  obtain ⟨hXl, hXr⟩ := isRect_spec _ _ X hX
  obtain ⟨hBll, hBlr⟩ := isRect_spec _ _ Bl hBl
  obtain ⟨hBrl, hBrr⟩ := isRect_spec _ _ Br hBr
  have hpar : ∀ mg ∈ gs, ∀ sg ∈ mg.2, ∀ p ∈ sg.2, KPar.ok p ∧ p.1 ∈ perms3 := by
    intro mg hm sg hs p hp
    exact ⟨((hmg mg hm).2 sg hs).2 p hp, (hgs mg hm sg hs p hp).1 ▸ ((hmg mg hm).2 sg hs).1⟩
  refine ⟨k0, k1, k2, kq, rfl, hpar, ?_⟩
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [foldl_add_sum, zero_add]
  congr 1
  refine mapM_sum _ _ gs vs ?_ hvs
  intro mg hm x hx
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hx
  -- the first level
  set n1 := k0 * k1 * k2
  set Y := Ymat k X Bl Br
  set T := nth (nth rhos 3 []) mg.1 [] with hTdef
  have hT3 := hrho 3 (by norm_num)
  have hTmem : T ∈ rhos.getD 3 [] := by
    have e : T = (rhos.getD 3 []).getD mg.1 [] := by rw [hTdef, nth_eq_getD, nth_eq_getD]
    rw [e, List.getD_eq_getElem (rhos.getD 3 []) [] (by rw [hT3.1]; exact (hmg mg hm).1)]
    exact List.getElem_mem _
  obtain ⟨hTl, hTr⟩ := hT3.2 T hTmem
  have hn : k0 * k1 * k2 * kq = kq * n1 := by ring
  obtain ⟨yl, ys⟩ := yRows_spec k w (kq * n1) X Bl Br hXl hXr (by rw [hBrl, hn]) hBrr
  have hym := Ymat_bound k X Bl Br hBlr hBrr
  have htm : ∀ c e, |ent T c e| ≤ ((maxNat ((nth rhos 3 []).map entMax) : ℕ) : ℤ) := by
    intro c e
    refine (ent_le_entMax T c e).trans ?_
    have : T ∈ nth rhos 3 [] := by rw [nth_eq_getD]; exact hTmem
    exact_mod_cast le_maxNat _ _ (List.mem_map.mpr ⟨T, this, rfl⟩)
  obtain ⟨Ll, Lr⟩ := level1C_spec w kq n1 bnd hw hkq T hTl hTr (yRows k w X Bl Br) (by rw [yl, hBll, hn])
    Y (fun i _ => ys i hBlr) _ _ htm hym (Nat.cast_nonneg _)
    (by have := Nat.cast_nonneg (α := ℤ) (rowSumMax Bl); have := Nat.cast_nonneg (α := ℤ) (entMax X);
        have := Nat.cast_nonneg (α := ℤ) (rowSumMax Br); positivity)
    (by exact_mod_cast hwb) (by exact_mod_cast hbnd) L hL
  have hLr : ∀ r ∈ L, r.length = n1 := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hr
    rw [← List.getD_eq_getElem _ [] ha]; exact (Lr a (Ll ▸ ha)).1
  -- the σ-groups
  rw [foldl_add_sum, zero_add]
  congr 1
  refine List.map_congr_left fun sg hsg => ?_
  simp only [sgroupVal, nth]
  rw [foldl_add_sum, zero_add]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨hσp, hmp⟩ := hgs mg hm sg hsg p hp
  have hσ := ((hmg mg hm).2 sg hsg).1
  rw [sgroup_rep β S1.length k0 k1 k2 kq hk0 hk1 hk2 sg.1 hσ p (((hmg mg hm).2 sg hsg).2 p hp) S1 hnd hlt
    rhos (fun f hf => hrho f (by omega)) L Ll hLr
    (fun a b => ∑ c ∈ range kq, ∑ e ∈ range kq, rhoE rhos 3 mg.1 c e * Y (a * kq + c) (b * kq + e))
    (fun a ha b hb => by
      rw [(Lr a ha).2 b hb]
      simp only [rhoE, hTdef, nth_eq_getD])]
  simp only [repVal, Fv, hσp, hmp]

end LayerDProto

#print axioms LayerDProto.ptab_grid
#print axioms LayerDProto.K3_perm
#print axioms LayerDProto.tensorP3_rep
#print axioms LayerDProto.sgroup_rep
#print axioms LayerDProto.partD_sound
