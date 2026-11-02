import LayerDProto.R2Part

/-!
# Layer D, (E′): the fold lemma and the soundness of the packed `K`-invariance check

`F ∘ κ = F` for a part's functional `F(t) = ⟨Y, ⊗_u ρ_u(t_u)⟩` (`Fv`), from the kernel checks
`foldTabOK` (the fold identities of the tables) and `foldBOK` (the packed `B`-level identities):

1. `Fv` in four-axis form (`Fd`, sums over index pairs of the four axes);
2. the fold: `Fd (Â_u ρ_u^{(τ)} Ĉ_u)_u Z = Fd (ρ_u)_u Z'` with `Z'(a, b) = ∑_{c, e} ∏_u Â_u[c_u][a_u] Ĉ_u[b_u][e_u] Z(c, e)`
   (indices swapped when transposed);
3. the axis permutation of `κ` (`K3_perm`);
4. the `B`-level check gives `Z' = α Y` (`foldBOK_spec`), hence `α F(κ t) = α F(t)`.
-/

open Finset

namespace LayerDProto

/-! ## Four-axis form -/

abbrev D4T := ℕ × ℕ × ℕ × ℕ
abbrev P4T := ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)

/-- Index pairs `(c, e)` of one axis. -/
def sq (k : ℕ) : Finset (ℕ × ℕ) := range k ×ˢ range k

/-- Index pairs of the four axes. -/
def P4 (k0 k1 k2 kq : ℕ) : Finset P4T := box k0 k1 k2 ×ˢ sq kq

/-- Multi-indices of the four axes. -/
def D4 (k0 k1 k2 kq : ℕ) : Finset D4T := range k0 ×ˢ range k1 ×ˢ range k2 ×ˢ range kq

def cOf (x : P4T) : D4T := (x.1.1.1, x.1.2.1.1, x.1.2.2.1, x.2.1)
def eOf (x : P4T) : D4T := (x.1.1.2, x.1.2.1.2, x.1.2.2.2, x.2.2)

/-- The Kronecker index of a multi-index. -/
def enc4 (k1 k2 kq : ℕ) (c : D4T) : ℕ := enc3 k1 k2 c.1 c.2.1 c.2.2.1 * kq + c.2.2.2

/-- `∑_{c, e} ∏_u R_u[c_u][e_u] Z(c, e)`. -/
def Fd (k0 k1 k2 kq : ℕ) (R0 R1 R2 R3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) : ℤ :=
  ∑ x ∈ P4 k0 k1 k2 kq, R0 x.1.1.1 x.1.1.2 * R1 x.1.2.1.1 x.1.2.1.2 * R2 x.1.2.2.1 x.1.2.2.2 *
    R3 x.2.1 x.2.2 * Z (cOf x) (eOf x)

theorem Fv_eq_Fd (k0 k1 k2 kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ) (s0 s1 s2 s3 : ℕ) :
    Fv k0 k1 k2 kq rhos Y s0 s1 s2 s3 = Fd k0 k1 k2 kq (rhoE rhos 0 s0) (rhoE rhos 1 s1) (rhoE rhos 2 s2)
      (rhoE rhos 3 s3) (fun c e => Y (enc4 k1 k2 kq c) (enc4 k1 k2 kq e)) := by
  unfold Fv K3 Fd P4 sq
  rw [sum_product]
  refine sum_congr rfl fun x _ => ?_
  beta_reduce
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [cOf, eOf, enc4]
  ring

/-- Pairs of the four axes are pairs of multi-indices. -/
theorem sum_P4 (k0 k1 k2 kq : ℕ) (F : D4T → D4T → ℤ) :
    ∑ x ∈ P4 k0 k1 k2 kq, F (cOf x) (eOf x) = ∑ c ∈ D4 k0 k1 k2 kq, ∑ e ∈ D4 k0 k1 k2 kq, F c e := by
  rw [← sum_product']
  refine sum_nbij' (fun x => (cOf x, eOf x))
    (fun y => (((y.1.1, y.2.1), (y.1.2.1, y.2.2.1), (y.1.2.2.1, y.2.2.2.1)), (y.1.2.2.2, y.2.2.2.2)))
    ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · intro x hx
    simp only [P4, box, sq, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio,
      mem_coe] at hx ⊢
    simp only [D4, cOf, eOf, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe]
    tauto
  · intro y hy
    simp only [D4, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio,
      mem_coe] at hy ⊢
    simp only [P4, box, sq, mem_product, mem_range, coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe]
    tauto

theorem Fd_congr (k0 k1 k2 kq : ℕ) (R0 R1 R2 R3 R0' R1' R2' R3' : ℕ → ℕ → ℤ) (Z Z' : D4T → D4T → ℤ)
    (h0 : ∀ c < k0, ∀ e < k0, R0 c e = R0' c e) (h1 : ∀ c < k1, ∀ e < k1, R1 c e = R1' c e)
    (h2 : ∀ c < k2, ∀ e < k2, R2 c e = R2' c e) (h3 : ∀ c < kq, ∀ e < kq, R3 c e = R3' c e)
    (hZ : ∀ c ∈ D4 k0 k1 k2 kq, ∀ e ∈ D4 k0 k1 k2 kq, Z c e = Z' c e) :
    Fd k0 k1 k2 kq R0 R1 R2 R3 Z = Fd k0 k1 k2 kq R0' R1' R2' R3' Z' := by
  refine sum_congr rfl fun x hx => ?_
  simp only [P4, box, sq, mem_product, mem_range] at hx
  obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩, e, f⟩, g, h⟩ := hx
  rw [h0 _ a _ b, h1 _ c _ d, h2 _ e _ f, h3 _ g _ h, hZ _ (by simp [D4, cOf, *]) _ (by simp [D4, eOf, *])]

theorem Fd_smul (k0 k1 k2 kq : ℕ) (a0 a1 a2 a3 : ℤ) (R0 R1 R2 R3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) :
    Fd k0 k1 k2 kq (fun c e => a0 * R0 c e) (fun c e => a1 * R1 c e) (fun c e => a2 * R2 c e)
      (fun c e => a3 * R3 c e) Z = a0 * a1 * a2 * a3 * Fd k0 k1 k2 kq R0 R1 R2 R3 Z := by
  unfold Fd
  simp only [Finset.mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem Fd_Zsmul (k0 k1 k2 kq : ℕ) (a : ℤ) (R0 R1 R2 R3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) :
    Fd k0 k1 k2 kq R0 R1 R2 R3 (fun c e => a * Z c e) = a * Fd k0 k1 k2 kq R0 R1 R2 R3 Z := by
  unfold Fd
  simp only [Finset.mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem mul_sums {α β : Type*} (s : Finset α) (t : Finset β) (f : α → ℤ) (g : β → ℤ) :
    (∑ i ∈ s, f i) * (∑ j ∈ t, g j) = ∑ p ∈ s ×ˢ t, f p.1 * g p.2 := by
  rw [sum_product, sum_mul_sum]

theorem prod4_sum {α : Type*} (s0 s1 s2 s3 : Finset α) (g0 g1 g2 g3 : α → ℤ) :
    (∑ y ∈ s0, g0 y) * (∑ y ∈ s1, g1 y) * (∑ y ∈ s2, g2 y) * (∑ y ∈ s3, g3 y) =
      ∑ y ∈ (s0 ×ˢ (s1 ×ˢ s2)) ×ˢ s3, g0 y.1.1 * g1 y.1.2.1 * g2 y.1.2.2 * g3 y.2 := by
  rw [mul_assoc (∑ y ∈ s0, g0 y), mul_sums s1 s2, mul_sums s0, mul_sums _ s3]
  exact sum_congr rfl fun _ _ => by ring

/-- Products of four sums over index pairs. -/
theorem Fd_expand (k0 k1 k2 kq : ℕ) (f0 f1 f2 f3 : ℕ × ℕ → ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) :
    Fd k0 k1 k2 kq (fun c e => ∑ y ∈ sq k0, f0 y c e) (fun c e => ∑ y ∈ sq k1, f1 y c e)
      (fun c e => ∑ y ∈ sq k2, f2 y c e) (fun c e => ∑ y ∈ sq kq, f3 y c e) Z =
    ∑ y ∈ P4 k0 k1 k2 kq, ∑ x ∈ P4 k0 k1 k2 kq, f0 y.1.1 x.1.1.1 x.1.1.2 * f1 y.1.2.1 x.1.2.1.1 x.1.2.1.2 *
      f2 y.1.2.2 x.1.2.2.1 x.1.2.2.2 * f3 y.2 x.2.1 x.2.2 * Z (cOf x) (eOf x) := by
  unfold Fd
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [prod4_sum, sum_mul]
  rfl

/-- **The fold, plain.** -/
theorem Fd_fold (k0 k1 k2 kq : ℕ) (A0 A1 A2 A3 R0 R1 R2 R3 C0 C1 C2 C3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) :
    Fd k0 k1 k2 kq (fun c e => ∑ y ∈ sq k0, A0 c y.1 * R0 y.1 y.2 * C0 y.2 e)
      (fun c e => ∑ y ∈ sq k1, A1 c y.1 * R1 y.1 y.2 * C1 y.2 e)
      (fun c e => ∑ y ∈ sq k2, A2 c y.1 * R2 y.1 y.2 * C2 y.2 e)
      (fun c e => ∑ y ∈ sq kq, A3 c y.1 * R3 y.1 y.2 * C3 y.2 e) Z =
    Fd k0 k1 k2 kq R0 R1 R2 R3 (fun a b => ∑ c ∈ D4 k0 k1 k2 kq, ∑ e ∈ D4 k0 k1 k2 kq,
      A0 c.1 a.1 * A1 c.2.1 a.2.1 * A2 c.2.2.1 a.2.2.1 * A3 c.2.2.2 a.2.2.2 *
      (C0 b.1 e.1 * C1 b.2.1 e.2.1 * C2 b.2.2.1 e.2.2.1 * C3 b.2.2.2 e.2.2.2) * Z c e) := by
  rw [Fd_expand]
  unfold Fd
  refine sum_congr rfl fun y _ => ?_
  beta_reduce
  rw [← sum_P4, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [cOf, eOf]
  ring

/-- **The fold, transposed.** -/
theorem Fd_foldT (k0 k1 k2 kq : ℕ) (A0 A1 A2 A3 R0 R1 R2 R3 C0 C1 C2 C3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) :
    Fd k0 k1 k2 kq (fun c e => ∑ y ∈ sq k0, A0 c y.1 * R0 y.2 y.1 * C0 y.2 e)
      (fun c e => ∑ y ∈ sq k1, A1 c y.1 * R1 y.2 y.1 * C1 y.2 e)
      (fun c e => ∑ y ∈ sq k2, A2 c y.1 * R2 y.2 y.1 * C2 y.2 e)
      (fun c e => ∑ y ∈ sq kq, A3 c y.1 * R3 y.2 y.1 * C3 y.2 e) Z =
    Fd k0 k1 k2 kq R0 R1 R2 R3 (fun a b => ∑ c ∈ D4 k0 k1 k2 kq, ∑ e ∈ D4 k0 k1 k2 kq,
      A0 c.1 b.1 * A1 c.2.1 b.2.1 * A2 c.2.2.1 b.2.2.1 * A3 c.2.2.2 b.2.2.2 *
      (C0 a.1 e.1 * C1 a.2.1 e.2.1 * C2 a.2.2.1 e.2.2.1 * C3 a.2.2.2 e.2.2.2) * Z c e) := by
  rw [Fd_expand]
  unfold Fd
  -- swap the two indices of every pair
  let sw : P4T → P4T := fun y =>
    (((y.1.1.2, y.1.1.1), (y.1.2.1.2, y.1.2.1.1), (y.1.2.2.2, y.1.2.2.1)), (y.2.2, y.2.1))
  have hsw : ∀ y ∈ P4 k0 k1 k2 kq, sw y ∈ P4 k0 k1 k2 kq := by
    intro y hy
    simp only [P4, box, sq, mem_product, mem_range, sw] at hy ⊢
    tauto
  refine sum_nbij' sw sw hsw hsw (fun _ _ => rfl) (fun _ _ => rfl) fun y _ => ?_
  beta_reduce
  rw [← sum_P4, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [cOf, eOf, sw]
  ring

/-! ## The table check -/

theorem ent_transp (k : ℕ) (L : List (List ℤ)) (hL : ∀ r ∈ L, r.length = k) (j i : ℕ) (hj : j < k) :
    ent (transp k L) j i = ent L i j :=
  (transp_spec k L hL).2 j hj i

theorem mm_spec (k : ℕ) (A B : List (List ℤ)) (hB : ∀ r ∈ B, r.length = k)
    (hA : ∀ r ∈ A, r.length = B.length) (i j : ℕ) (hj : j < k) :
    ent (mm k A B) i j = ∑ p ∈ range B.length, ent A i p * ent B p j := by
  unfold ent mm
  by_cases hi : i < A.length
  · rw [List.getD_eq_getElem _ [] (by simpa using hi), List.getElem_map,
      getD_map_zero (dot A[i]) (transp k B) [] (by cases A[i] <;> rfl) j, dot_eq,
      hA _ (List.getElem_mem hi)]
    refine sum_congr rfl fun p _ => ?_
    rw [(transp_spec k B hB).2 j hj p, List.getD_eq_getElem _ [] hi]
  · have h0 : (A.map fun r => (transp k B).map (dot r)).getD i [] = [] :=
      List.getD_eq_default _ _ (by simpa using hi)
    have : ∀ p, (A.getD i []).getD p 0 = 0 := fun p => by
      rw [List.getD_eq_default _ _ (not_lt.mp hi)]; simp
    rw [h0, List.getD_nil]
    exact (sum_eq_zero fun p _ => by rw [this p, zero_mul]).symm

theorem mm_length (k : ℕ) (A B : List (List ℤ)) : (mm k A B).length = A.length := by simp [mm]

theorem mm_rows (k : ℕ) (A B : List (List ℤ)) (hB : ∀ r ∈ B, r.length = k) :
    ∀ r ∈ mm k A B, r.length = k := by
  intro r hr
  simp only [mm, List.mem_map] at hr
  obtain ⟨a, _, rfl⟩ := hr
  simp [(transp_spec k B hB).1]

theorem ent_scaleM (a : ℤ) (M : List (List ℤ)) (i j : ℕ) : ent (scaleM a M) i j = a * ent M i j := by
  unfold ent scaleM
  have h1 : (M.map (·.map (a * ·))).getD i [] = (M.getD i []).map (a * ·) := by
    have := getD_map_list (fun r : List ℤ => r.map (a * ·)) M [] i
    simpa using this
  rw [h1, getD_map_zero (a * ·) _ 0 (by simp) j]

/-- The transposition flag on a table. -/
def tflip (τ : Bool) (R : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ := fun p q => if τ then R q p else R p q

/-- What `foldTabOK` guarantees: equal dimensions and the fold identities of the four axes. -/
theorem foldTabOK_spec (ks : List ℕ) (rhos : List (List (List (List ℤ)))) (κ : KPar) (τ : Bool)
    (As Cs : List (List (List ℤ))) (als : List ℤ) (h : foldTabOK ks rhos κ τ As Cs als = true) :
    rhosOK ks rhos = true ∧ κ.1 ∈ perms3 ∧ KPar.ok κ ∧ ∀ u < 4,
      nth ks (nth (inv3 κ.1 ++ [3]) u 0) 1 = nth ks u 1 ∧ ∀ s < 24, ∀ c < nth ks u 1, ∀ e < nth ks u 1,
        ∑ y ∈ sq (nth ks u 1), ent (nth As u []) c y.1 * tflip τ (rhoE rhos u s) y.1 y.2 *
          ent (nth Cs u []) y.2 e = nth als u 0 * rhoE rhos (nth (inv3 κ.1 ++ [3]) u 0) (kact κ s) c e := by
  simp only [foldTabOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem, beq_iff_eq, and_assoc] at h
  obtain ⟨hr, hp, hg, hg', hu⟩ := h
  refine ⟨hr, hp, ⟨hg, hg'⟩, fun u hu4 => ?_⟩
  obtain ⟨hdim, hA, hC, hs⟩ := hu u hu4
  refine ⟨hdim, fun s hs24 c hc e he => ?_⟩
  set k := nth ks u 1
  set A := nth As u [] with hAdef
  set C := nth Cs u [] with hCdef
  obtain ⟨hAl, hAr⟩ := isRect_spec _ _ _ hA
  obtain ⟨hCl, hCr⟩ := isRect_spec _ _ _ hC
  have hrs := (rhosOK_spec ks rhos hr) u hu4
  set R := nth (nth rhos u []) s [] with hRdef
  have hRm : R ∈ rhos.getD u [] := by
    have e : R = (rhos.getD u []).getD s [] := by rw [hRdef, nth_eq_getD, nth_eq_getD]
    rw [e, List.getD_eq_getElem (rhos.getD u []) [] (by rw [hrs.1]; exact hs24)]
    exact List.getElem_mem _
  obtain ⟨hRl, hRr⟩ := hrs.2 R hRm
  have hent := congrArg (fun M => ent M c e) (hs s hs24)
  simp only at hent
  have hRt : ∀ r ∈ (if τ then transp k R else R), r.length = k := by
    cases τ
    · simpa using hRr
    · intro r hr; simp only [if_true] at hr; rw [transp_row_length k R hRr r hr, hRl]
  have hRtl : (if τ then transp k R else R).length = k := by
    cases τ
    · simpa using hRl
    · simp [(transp_spec k R hRr).1]
  rw [mm_spec k _ C hCr (fun r hr => by rw [mm_rows k _ _ hRt r hr, hCl]) c e he, ent_scaleM] at hent
  rw [show rhoE rhos (nth (inv3 κ.1 ++ [3]) u 0) (kact κ s) c e =
      ent (nth (nth rhos (nth (inv3 κ.1 ++ [3]) u 0) []) (kact κ s) []) c e by
    simp only [rhoE, nth_eq_getD], ← hent, hCl, sq, sum_product, sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [mm_spec k A _ hRt (fun r hr => by rw [hAr r hr, hRtl]) c p (mem_range.mp hp), hRtl, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  congr 2
  unfold tflip rhoE
  rw [← nth_eq_getD, ← nth_eq_getD, ← hRdef]
  cases τ
  · rfl
  · simp only [if_true]
    exact (ent_transp k R hRr q p (mem_range.mp hq)).symm

/-! ## The packed `B`-level products -/

theorem flatMap_range_getD {α : Type} (N : ℕ) (f : ℕ → List α) (hf : ∀ a, (f a).length = N) (d : α) :
    ∀ k, ((List.range k).flatMap f).length = k * N ∧
      ∀ a < k, ∀ x < N, ((List.range k).flatMap f).getD (a * N + x) d = (f a).getD x d
  | 0 => by simp
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := flatMap_range_getD N f hf d k
    have e : (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
      simp [List.range_succ, List.flatMap_append]
    rw [e]
    refine ⟨by rw [List.length_append, ih1, hf]; ring, fun a ha x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
    · rw [List.getD_append _ _ _ _ (by rw [ih1]; nlinarith), ih2 a ha x hx]
    · rw [List.getD_append_right _ _ _ _ (by rw [ih1]; omega), ih1]
      congr 1; omega

theorem dot_nil_right (l : List ℤ) : dot l [] = 0 := by cases l <;> rfl

/-- `out[a N + x] = ∑_c A[c][a] P[x k + c]`. -/
theorem rotApply_spec (k N : ℕ) (hk : 0 < k) (A : List (List ℤ)) (hA : A.length = k) (P : List ℤ)
    (hP : P.length = k * N) :
    (rotApply k A P).length = k * N ∧ ∀ a < k, ∀ x < N,
      (rotApply k A P).getD (a * N + x) 0 = ∑ c ∈ range k, ent A c a * P.getD (x * k + c) 0 := by
  obtain ⟨c1, c2⟩ := chunks_spec k hk N P.length P hP (by rw [hP]; nlinarith)
  have hf : ∀ a, ((chunks k P.length P).map (dot (A.map fun r => nth r a 0))).length = N := by
    intro a; rw [List.length_map, c1]
  obtain ⟨f1, f2⟩ := flatMap_range_getD N _ hf 0 k
  refine ⟨f1, fun a ha x hx => ?_⟩
  unfold rotApply
  rw [f2 a ha x hx, getD_map_zero _ _ [] (dot_nil_right _) x, c2 x hx, dot_eq, List.length_map, hA]
  refine sum_congr rfl fun c hc => ?_
  rw [getD_map_zero (fun r => nth r a 0) A [] (by rfl) c, nth_eq_getD,
    getD_take_drop _ _ _ _ (mem_range.mp hc)]
  rfl

theorem pk_nil (w : ℕ) : pk w [] = 0 := rfl

/-- The row map of `foldRows`: multi-index `c` (new order) to the row of `B`. -/
def pidx (k0 k1 k2 kq : ℕ) (σ : List ℕ) (c : D4T) : ℕ :=
  (permIdx3 [k0, k1, k2, kq] σ).getD (enc3 k1 k2 c.1 c.2.1 c.2.2.1) 0 * kq + c.2.2.2

/-- **`Λ P_σ B`.** -/
theorem foldRows_spec (w k0 k1 k2 kq : ℕ) (hk0 : 0 < k0) (hk1 : 0 < k1) (hk2 : 0 < k2) (hkq : 0 < kq)
    (σ : List ℕ) (hσ : σ ∈ perms3) (As : List (List (List ℤ)))
    (hAs : ∀ u < 4, (nth As u []).length = nth [k0, k1, k2, kq] u 1) (B : List (List ℤ)) :
    (foldRows w [k0, k1, k2, kq] σ As B).length = k0 * k1 * k2 * kq ∧
    ∀ a ∈ D4 k0 k1 k2 kq, (foldRows w [k0, k1, k2, kq] σ As B).getD (enc4 k1 k2 kq a) 0 =
      ∑ c ∈ D4 k0 k1 k2 kq, ent (nth As 0 []) c.1 a.1 * ent (nth As 1 []) c.2.1 a.2.1 *
        ent (nth As 2 []) c.2.2.1 a.2.2.1 * ent (nth As 3 []) c.2.2.2 a.2.2.2 *
        pk w (B.getD (pidx k0 k1 k2 kq σ c) []) := by
  obtain ⟨il, -⟩ := permIdx3_props k0 k1 k2 kq σ hσ
  set P := (permIdx4 [k0, k1, k2, kq] σ).map fun i => nth (B.map (pk w)) i 0 with hPdef
  have hPl : P.length = kq * (k0 * k1 * k2) := by
    simp [hPdef, permIdx4, nth, il, mul_comm]
  have hPg : ∀ x < k0 * k1 * k2, ∀ cq < kq, P.getD (x * kq + cq) 0 =
      pk w (B.getD ((permIdx3 [k0, k1, k2, kq] σ).getD x 0 * kq + cq) []) := by
    intro x hx cq hcq
    have hi : x * kq + cq < (permIdx4 [k0, k1, k2, kq] σ).length := by
      simp only [permIdx4, nth, List.length_map, List.length_range, il]; nlinarith
    rw [hPdef, List.getD_eq_getElem _ 0 (by simpa using hi), List.getElem_map, nth_eq_getD,
      getD_map_zero (pk w) B [] (pk_nil w)]
    congr 2
    simp only [permIdx4, nth, List.getElem_map, List.getElem_range, nth_eq_getD]
    have h1 : (x * kq + cq) / kq = x := by
      rw [add_comm, Nat.add_mul_div_right _ _ hkq, Nat.div_eq_of_lt hcq, zero_add]
    have h2 : (x * kq + cq) % kq = cq := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcq]
    rw [h1, h2]
  have r1 := rotApply_spec kq (k0 * k1 * k2) hkq _ (hAs 3 (by norm_num)) P hPl
  have r2 := rotApply_spec k2 (kq * k0 * k1) hk2 _ (hAs 2 (by norm_num)) _ (by rw [r1.1]; ring)
  have r3 := rotApply_spec k1 (k2 * kq * k0) hk1 _ (hAs 1 (by norm_num)) _ (by rw [r2.1]; ring)
  have r4 := rotApply_spec k0 (k1 * k2 * kq) hk0 _ (hAs 0 (by norm_num)) _ (by rw [r3.1]; ring)
  have hF : foldRows w [k0, k1, k2, kq] σ As B = rotApply k0 (nth As 0 []) (rotApply k1 (nth As 1 [])
      (rotApply k2 (nth As 2 []) (rotApply kq (nth As 3 []) P))) := rfl
  refine ⟨by rw [hF, r4.1]; ring, fun a ha => ?_⟩
  simp only [D4, mem_product, mem_range] at ha
  obtain ⟨ha0, ha1, ha2, haq⟩ := ha
  show (rotApply k0 (nth As 0 []) (rotApply k1 (nth As 1 []) (rotApply k2 (nth As 2 [])
    (rotApply kq (nth As 3 []) P)))).getD (enc4 k1 k2 kq a) 0 = _
  have e4 : enc4 k1 k2 kq a = a.1 * (k1 * k2 * kq) + ((a.2.1 * k2 + a.2.2.1) * kq + a.2.2.2) := by
    simp only [enc4, enc3]; ring
  rw [e4, r4.2 _ ha0 ((a.2.1 * k2 + a.2.2.1) * kq + a.2.2.2) (enc3_lt ha1 ha2 haq), D4, sum_product]
  refine sum_congr rfl fun c0 hc0 => ?_
  have hc0' := mem_range.mp hc0
  rw [show ((a.2.1 * k2 + a.2.2.1) * kq + a.2.2.2) * k0 + c0 =
      a.2.1 * (k2 * kq * k0) + ((a.2.2.1 * kq + a.2.2.2) * k0 + c0) by ring,
    r3.2 _ ha1 ((a.2.2.1 * kq + a.2.2.2) * k0 + c0) (enc3_lt ha2 haq hc0'), sum_product, mul_sum]
  refine sum_congr rfl fun c1 hc1 => ?_
  have hc1' := mem_range.mp hc1
  rw [show ((a.2.2.1 * kq + a.2.2.2) * k0 + c0) * k1 + c1 =
      a.2.2.1 * (kq * k0 * k1) + ((a.2.2.2 * k0 + c0) * k1 + c1) by ring,
    r2.2 _ ha2 ((a.2.2.2 * k0 + c0) * k1 + c1) (enc3_lt haq hc0' hc1'), sum_product, mul_sum, mul_sum]
  refine sum_congr rfl fun c2 hc2 => ?_
  have hc2' := mem_range.mp hc2
  rw [show ((a.2.2.2 * k0 + c0) * k1 + c1) * k2 + c2 =
      a.2.2.2 * (k0 * k1 * k2) + ((c0 * k1 + c1) * k2 + c2) by ring,
    r1.2 _ haq ((c0 * k1 + c1) * k2 + c2) (enc3_lt hc0' hc1' hc2'), mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun cq hcq => ?_
  rw [hPg ((c0 * k1 + c1) * k2 + c2) (enc3_lt hc0' hc1' hc2') _ (mem_range.mp hcq)]
  simp only [pidx, enc3]
  ring

/-! ## Soundness of `foldBOK` -/

theorem sum4_swap {α β γ δ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
    (f : α → β → γ → δ → ℤ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w = ∑ z ∈ u, ∑ w ∈ v, ∑ x ∈ s, ∑ y ∈ t, f x y z w := by
  calc ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w
      = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, ∑ w ∈ v, f x y z w := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ x ∈ s, ∑ z ∈ u, ∑ w ∈ v, ∑ y ∈ t, f x y z w :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ z ∈ u, ∑ x ∈ s, ∑ w ∈ v, ∑ y ∈ t, f x y z w := sum_comm
    _ = ∑ z ∈ u, ∑ w ∈ v, ∑ x ∈ s, ∑ y ∈ t, f x y z w := sum_congr rfl fun _ _ => sum_comm

theorem triple_sum {α β : Type*} (s : Finset α) (t : Finset β) (u : α → ℤ) (v : β → ℤ) (x : ℤ) :
    (∑ c ∈ s, u c) * x * (∑ e ∈ t, v e) = ∑ c ∈ s, ∑ e ∈ t, u c * x * v e := by
  rw [sum_mul, sum_mul]
  exact sum_congr rfl fun c _ => by rw [mul_sum]

theorem alg1 (D : Finset D4T) (fA fC : D4T → ℤ) (pid : D4T → ℕ) (k : ℕ) (Bl X Br : ℕ → ℕ → ℤ) :
    ∑ c ∈ D, ∑ e ∈ D, fA c * fC e * (∑ p ∈ range k, ∑ q ∈ range k, Bl (pid c) p * X p q * Br (pid e) q) =
      ∑ p ∈ range k, ∑ q ∈ range k, (∑ c ∈ D, fA c * Bl (pid c) p) * X p q *
        (∑ e ∈ D, fC e * Br (pid e) q) := by
  conv_lhs => simp only [mul_sum]
  rw [sum4_swap]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  rw [triple_sum]
  refine sum_congr rfl fun c _ => sum_congr rfl fun e _ => ?_
  ring

theorem alg2 (k : ℕ) (Bl Br X Q R : ℕ → ℕ → ℤ) (i j : ℕ) :
    ∑ p ∈ range k, ∑ q ∈ range k, (∑ p' ∈ range k, Bl i p' * Q p p') * X p q *
        (∑ q' ∈ range k, Br j q' * R q q') =
      ∑ p' ∈ range k, ∑ q' ∈ range k, Bl i p' *
        (∑ p ∈ range k, ∑ q ∈ range k, Q p p' * X p q * R q q') * Br j q' := by
  conv_rhs => simp only [mul_sum, sum_mul]
  have : ∀ p q, (∑ p' ∈ range k, Bl i p' * Q p p') * X p q * (∑ q' ∈ range k, Br j q' * R q q') =
      ∑ p' ∈ range k, ∑ q' ∈ range k, Bl i p' * Q p p' * X p q * (Br j q' * R q q') :=
    fun p q => triple_sum _ _ _ _ _
  simp only [this]
  rw [sum4_swap]
  refine sum_congr rfl fun p' _ => sum_congr rfl fun q' _ => sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  ring

theorem digits_of_eq (w k : ℕ) (x y : ℕ → ℤ) (Dx Dy : ℕ) (hx : ∀ p < k, |x p| ≤ Dx)
    (hy : ∀ p < k, |y p| ≤ Dy) (hDx : 4 * Dx < 2 ^ w) (hDy : 4 * Dy < 2 ^ w)
    (h : ∑ p ∈ range k, x p * 2 ^ (w * p) = ∑ p ∈ range k, y p * 2 ^ (w * p)) : ∀ p < k, x p = y p := by
  have hp : ∀ p, (2 : ℤ) ^ (w * p) = (2 ^ w) ^ p := fun p => pow_mul 2 w p
  simp only [hp] at h
  refine digits_unique (2 ^ w) (one_le_pow₀ (by norm_num)) x y k (fun p hpk => ?_) (fun p hpk => ?_) h
  · have := hx p hpk
    have h2 : (4 * Dx : ℤ) < 2 ^ w := by exact_mod_cast hDx
    linarith
  · have := hy p hpk
    have h2 : (4 * Dy : ℤ) < 2 ^ w := by exact_mod_cast hDy
    linarith

theorem card_D4 (k0 k1 k2 kq : ℕ) : (D4 k0 k1 k2 kq).card = k0 * k1 * k2 * kq := by
  simp [D4, card_product]; ring

theorem bound_D4 (k0 k1 k2 kq : ℕ) (f : D4T → ℤ) (M : ℤ) (h : ∀ c ∈ D4 k0 k1 k2 kq, |f c| ≤ M) :
    |∑ c ∈ D4 k0 k1 k2 kq, f c| ≤ ((k0 * k1 * k2 * kq : ℕ) : ℤ) * M := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have := sum_le_sum h
  rw [sum_const, card_D4, nsmul_eq_mul] at this
  exact this

theorem abs_ent4 (A0 A1 A2 A3 B : List (List ℤ)) (x0 y0 x1 y1 x2 y2 x3 y3 i p : ℕ) :
    |ent A0 x0 y0 * ent A1 x1 y1 * ent A2 x2 y2 * ent A3 x3 y3 * ent B i p| ≤
      ((entMax A0 * entMax A1 * entMax A2 * entMax A3 : ℕ) : ℤ) * entMax B := by
  simp only [abs_mul, Nat.cast_mul]
  gcongr
  · exact ent_le_entMax _ _ _
  · exact ent_le_entMax _ _ _
  · exact ent_le_entMax _ _ _
  · exact ent_le_entMax _ _ _
  · exact ent_le_entMax _ _ _

/-- `B Qᵀ`, packed rows. -/
theorem mulTP_spec (k w : ℕ) (B Q : List (List ℤ)) (hB : ∀ r ∈ B, r.length = k) (hQ : Q.length = k)
    (hQr : ∀ r ∈ Q, r.length = k) (i : ℕ) :
    (mulTP k w B Q).getD i 0 = ∑ p ∈ range k, (∑ q ∈ range k, ent B i q * ent Q p q) * 2 ^ (w * p) := by
  obtain ⟨hc1, hc2⟩ := colPack_spec k w Q hQr
  rw [mulTP, getD_map_zero _ B [] (by rfl)]
  by_cases hi : i < B.length
  · have hlen : (B.getD i []).length = k := hB _ (by rw [List.getD_eq_getElem _ [] hi]; exact List.getElem_mem _)
    rw [dot_eq, hlen]
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun q hq => ?_
    rw [hc2 q (mem_range.mp hq), hQ, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp only [ent]; ring
  · have : B.getD i [] = [] := List.getD_eq_default _ _ (not_lt.mp hi)
    have h0 : ∀ q, ent B i q = 0 := fun q => by simp only [ent, this, List.getD_nil]
    simp only [this, dot, h0, zero_mul, sum_const_zero]

/-- The folded matrix `Z'(a, b) = ∑_{c, e} ∏_u A_u[c_u][a_u] C_u[b_u][e_u] Z(c, e)`. -/
def foldW (k0 k1 k2 kq : ℕ) (A0 A1 A2 A3 C0 C1 C2 C3 : ℕ → ℕ → ℤ) (Z : D4T → D4T → ℤ) (a b : D4T) : ℤ :=
  ∑ c ∈ D4 k0 k1 k2 kq, ∑ e ∈ D4 k0 k1 k2 kq,
    A0 c.1 a.1 * A1 c.2.1 a.2.1 * A2 c.2.2.1 a.2.2.1 * A3 c.2.2.2 a.2.2.2 *
      (C0 b.1 e.1 * C1 b.2.1 e.2.1 * C2 b.2.2.1 e.2.2.1 * C3 b.2.2.2 e.2.2.2) * Z c e

end LayerDProto

#print axioms LayerDProto.Fd_fold
#print axioms LayerDProto.Fd_foldT
#print axioms LayerDProto.foldTabOK_spec
#print axioms LayerDProto.foldRows_spec
