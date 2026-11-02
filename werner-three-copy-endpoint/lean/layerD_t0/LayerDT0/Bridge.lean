import LayerDT0.Assemble
import LayerDProto.R2Assembly

/-!
# Layer D (t = 0): the bridge from `BlockSpec.L` to the route-2′ part functionals

`IdentityT0` pairs each multiplier `X_b` with the block value `BlockSpec.L μ`. Route 2′
(`layerD_proto`) proves identities of the form `∑_t (∑_P fac_P · FTP P t) x_t = 0`, where `FTP P` is a
part's integer functional `⟨B_l X B_rᵀ, ρ₀(t₀) ⊗ ρ₁(t₁) ⊗ ρ₂(t₂) ⊗ ρ_q(t_q)⟩` read from lists.

* `pair_congr`, `pair_blockOp`, `pair_coupled`: linear algebra. `⟨X, Bᵀ M B⟩ = ⟨B X Bᵀ, M⟩`; the pairing
  with `blockOp` is `∑_s m(s) ⟨Z, ⊗ N(mp sᵢ) ⊗ Fq(mp s_q)⟩`; a coupled block splits into its three
  families (with `Xᵀ = X`, the `22` part counted twice).
* `pair_rtens_Fv`: the index layout. If `Z` is an integer matrix `Y` (divided by `c`) in the verifier's flat
  order `((a₀ k₁ + a₁) k₂ + a₂) k_q + c` and the factors are the list tables `rhoE rhos`, then
  `⟨Z, ⊗ A ⊗ S⟩ = Fv … / c`.
* `rhoSite`, `rhoMap`, `partRhos`: the tables of a block code, at `t = 0`.
* **`pair_word`, `pair_c3`, `pair_c23`** (the bridge): for a block code and any `X` with an integer
  version `ent Xint p q = c · X p q`, `⟨X, L_b(μ)⟩ = ∑_s μ_f(s) FTP P s / c` for every part data `P` whose
  `ks`, `k`, `X`, `B_l`, `B_r`, `rhos` are the block's.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint LayerDProto

/-! ### Linear algebra -/

theorem sum4_swap {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (F : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum3_rot {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (F : α → β → γ → M) : ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

theorem congr_apply {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) (M : Matrix m m ℝ)
    (i i' : n) : (Bᵀ * M * B) i i' = ∑ x, ∑ y, B x i * M x y * B y i' := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem pair_congr {m n : Type*} [Fintype m] [Fintype n] (X : Matrix n n ℝ) (B : Matrix m n ℝ)
    (M : Matrix m m ℝ) :
    ∑ i, ∑ i', X i i' * (Bᵀ * M * B) i i' = ∑ x, ∑ y, (B * X * Bᵀ) x y * M x y := by
  have R : ∀ x y, (B * X * Bᵀ) x y = ∑ i, ∑ i', B x i * X i i' * B y i' := by
    intro x y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [congr_apply, R, Finset.mul_sum, Finset.sum_mul]
  rw [sum4_swap]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

theorem blockOp_apply {K : Fin 3 → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (N : (i : Fin 3) → P4 → Matrix (K i) (K i) ℝ) (Fq : P4 → Matrix Kq Kq ℝ) (mp : P4 ≃ P4)
    (m : Tup (Fin 3) → ℝ) (x y : ((i : Fin 3) → K i) × Kq) :
    blockOp N Fq mp m x y = ∑ s, m s * rtens (fun i => N i (mp (s.1 i))) (Fq (mp s.2)) x y := by
  unfold blockOp
  rw [Matrix.sum_apply]
  rfl

theorem pair_blockOp {K : Fin 3 → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (Z : Matrix (((i : Fin 3) → K i) × Kq) (((i : Fin 3) → K i) × Kq) ℝ)
    (N : (i : Fin 3) → P4 → Matrix (K i) (K i) ℝ) (Fq : P4 → Matrix Kq Kq ℝ) (mp : P4 ≃ P4)
    (m : Tup (Fin 3) → ℝ) :
    ∑ x, ∑ y, Z x y * blockOp N Fq mp m x y =
      ∑ s, m s * ∑ x, ∑ y, Z x y * rtens (fun i => N i (mp (s.1 i))) (Fq (mp s.2)) x y := by
  simp only [blockOp_apply, Finset.mul_sum]
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The coupled pairing: `⟨X, [Bu; Bv]ᵀ [[A, C], [Cᵀ, D]] [Bu; Bv]⟩` for symmetric `X`. -/
theorem pair_coupled {m n : Type*} [Fintype m] [Fintype n] (X : Matrix n n ℝ) (hX : Xᵀ = X)
    (Bu Bv : Matrix m n ℝ) (A C D : Matrix m m ℝ) :
    ∑ i, ∑ i', X i i' * ((fromRows Bu Bv)ᵀ * fromBlocks A C Cᵀ D * fromRows Bu Bv) i i' =
      ∑ x, ∑ y, (Bu * X * Buᵀ) x y * A x y + 2 * ∑ x, ∑ y, (Bu * X * Bvᵀ) x y * C x y +
        ∑ x, ∑ y, (Bv * X * Bvᵀ) x y * D x y := by
  rw [pair_congr]
  have hs : ∑ x, ∑ y, (Bv * X * Buᵀ) x y * Cᵀ x y = ∑ x, ∑ y, (Bu * X * Bvᵀ) x y * C x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    · conv_rhs => rw [← hX]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  simp only [Fintype.sum_sum_type, Matrix.transpose_fromRows, Matrix.fromRows_mul,
    Matrix.mul_fromCols, fromRows_apply_inl, fromRows_apply_inr, fromCols_apply_inl,
    fromCols_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Finset.sum_add_distrib]
  rw [← hs]
  ring

/-! ### The index layout -/

/-- `(∏ᵢ Fin kᵢ) ≃ Fin k₀ × Fin k₁ × Fin k₂`. -/
def tup3Equiv (k : Fin 3 → ℕ) : ((i : Fin 3) → Fin (k i)) ≃ Fin (k 0) × Fin (k 1) × Fin (k 2) where
  toFun x := (x 0, x 1, x 2)
  invFun y := fun i => match i with
    | ⟨0, _⟩ => y.1
    | ⟨1, _⟩ => y.2.1
    | ⟨2, _⟩ => y.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

theorem sum_tup3 {M : Type*} [AddCommMonoid M] (k : Fin 3 → ℕ) (g : ((i : Fin 3) → Fin (k i)) → M) :
    ∑ x, g x = ∑ a0 : Fin (k 0), ∑ a1 : Fin (k 1), ∑ a2 : Fin (k 2), g ((tup3Equiv k).symm (a0, a1, a2)) := by
  rw [← (tup3Equiv k).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Fintype.sum_prod_type]

theorem tup3_symm_0 (k : Fin 3 → ℕ) (y : Fin (k 0) × Fin (k 1) × Fin (k 2)) : (tup3Equiv k).symm y 0 = y.1 := rfl
theorem tup3_symm_1 (k : Fin 3 → ℕ) (y : Fin (k 0) × Fin (k 1) × Fin (k 2)) : (tup3Equiv k).symm y 1 = y.2.1 := rfl
theorem tup3_symm_2 (k : Fin 3 → ℕ) (y : Fin (k 0) × Fin (k 1) × Fin (k 2)) : (tup3Equiv k).symm y 2 = y.2.2 := rfl

theorem sum4_rot {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (F : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d :=
        Finset.sum_congr rfl fun a _ => sum3_rot _
    _ = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := Finset.sum_comm

/-- **The index layout.** A matrix `Z` that is an integer matrix `Y / c` in the verifier's flat order,
paired with `(⊗ᵢ Aᵢ) ⊗ S` for list tables `Aᵢ = ρᵢ(jᵢ)`, `S = ρ_q(j_q)`, is the part functional `Fv`. -/
theorem pair_rtens_Fv (k : Fin 3 → ℕ) (kq : ℕ) (rhos : List (List (List (List ℤ)))) (Y : ℕ → ℕ → ℤ)
    (c : ℝ) (Z : Matrix (((i : Fin 3) → Fin (k i)) × Fin kq) (((i : Fin 3) → Fin (k i)) × Fin kq) ℝ)
    (hZ : ∀ x y, Z x y =
      (Y (flatIdx k kq (fun i => x.1 i) x.2) (flatIdx k kq (fun i => y.1 i) y.2) : ℝ) / c)
    (A : (i : Fin 3) → Matrix (Fin (k i)) (Fin (k i)) ℝ) (S : Matrix (Fin kq) (Fin kq) ℝ)
    (j : Fin 3 → ℕ) (jq : ℕ) (hA : ∀ i a b, A i a b = (rhoE rhos i (j i) a b : ℝ))
    (hS : ∀ a b, S a b = (rhoE rhos 3 jq a b : ℝ)) :
    ∑ x, ∑ y, Z x y * rtens A S x y = (Fv (k 0) (k 1) (k 2) kq rhos Y (j 0) (j 1) (j 2) jq : ℝ) / c := by
  rw [Fv, K3_nested]
  push_cast
  simp only [Finset.sum_range, Finset.mul_sum, Finset.sum_div]
  simp only [Fintype.sum_prod_type, sum_tup3 k, rtens, Matrix.of_apply, Fin.prod_univ_three, hA, hS,
    hZ, tup3_symm_0, tup3_symm_1, tup3_symm_2, Fin.val_zero, Fin.val_one, Fin.val_two]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun b0 _ => Finset.sum_congr rfl fun a1 _ => ?_
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun a2 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b2 _ => Finset.sum_congr rfl fun cq _ => Finset.sum_congr rfl fun eq _ => ?_
  have e0 : ((tup3Equiv k).symm (a0, a1, a2) 0 : ℕ) = a0 := rfl
  have e1 : ((tup3Equiv k).symm (a0, a1, a2) 1 : ℕ) = a1 := rfl
  have e2 : ((tup3Equiv k).symm (a0, a1, a2) 2 : ℕ) = a2 := rfl
  have f0 : ((tup3Equiv k).symm (b0, b1, b2) 0 : ℕ) = b0 := rfl
  have f1 : ((tup3Equiv k).symm (b0, b1, b2) 1 : ℕ) = b1 := rfl
  have f2 : ((tup3Equiv k).symm (b0, b1, b2) 2 : ℕ) = b2 := rfl
  simp only [flatIdx, e0, e1, e2, f0, f1, f2]
  ring_nf

/-! ### Diagram indices -/

theorem permEquiv_symm_val (p : P4) : ((permEquiv.symm p : Fin 24) : ℕ) = permIdx p := by
  conv_rhs => rw [← permEquiv.apply_symm_apply p, permEquiv_apply, permIdx_permTab]

theorem permIdx_mpE (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) (p : P4) :
    permIdx (mpE m hm p) = m (WernerEndpoint.fin24 (permIdx p)) := by
  obtain ⟨i, rfl⟩ := permTab_surj p
  rw [mpE_apply, permMap_permTab, permIdx_permTab, permIdx_permTab, fin24_val]

/-- A part's functional at a tuple of permutations is `Fv` at their indices. -/
theorem FTP_eq (P : PartData) (k0 k1 k2 kq : ℕ) (hks : P.ks = [k0, k1, k2, kq]) (s : Tup (Fin 3)) :
    FTP P s = Fv k0 k1 k2 kq P.rhos (Ymat P.k P.X P.Bl P.Br) (permIdx (s.1 0)) (permIdx (s.1 1))
      (permIdx (s.1 2)) (permIdx s.2) := by
  simp only [FTP, FT, FI, hks, nth]
  rw [← permEquiv_symm_val, ← permEquiv_symm_val, ← permEquiv_symm_val, ← permEquiv_symm_val]
  rfl

/-! ### The tables of a block code -/

theorem getD_map' {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : α) (d' : β) (h : f d = d') :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [h]

/-- The `t = 0` table of a site module: the constant coefficients of its `N`. -/
def rhoSite (s : SiteData) : List (List (List ℤ)) := s.N.map fun M => M.map fun r => r.map fun l => l.headD 0

/-- Tables re-indexed by a diagram map: entry `j` is the table at `m j`. -/
def rhoMap (m : Fin 24 → Fin 24) (rho : List (List (List ℤ))) : List (List (List ℤ)) :=
  (List.range 24).map fun j => rho.getD (m (WernerEndpoint.fin24 j)) []

/-- The four tables of a block code (sites 0, 1, 2 at `t = 0`, then the qubit module). -/
def partRhos (cuts : ℕ → CutData) (b : BCode) : List (List (List (List ℤ))) :=
  [rhoSite (b.site cuts 0), rhoSite (b.site cuts 1), rhoSite (b.site cuts 2), (b.qub cuts).F]

/-- The rows of a packed basis. -/
def basisRows (b : BCode) (P : List ℤ) : List (List ℤ) := P.map (unpk b.bb b.ncol)

theorem eval_toP_zero (l : List ℤ) : ((toP l).map (Int.castRingHom ℝ)).eval 0 = ((l.headD 0 : ℤ) : ℝ) := by
  cases l <;> simp [toP]

theorem rhoE_partRhos_site (cuts : ℕ → CutData) (b : BCode) (n : ℕ) (i : Fin 3) (p : P4)
    (a c : Fin ((b.toSpec cuts n).k i)) :
    (b.toSpec cuts n).N0 i p a c = (rhoE (partRhos cuts b) i (permIdx p) a c : ℝ) := by
  have e : ∀ (sd : SiteData) (j x y : ℕ), ent ((rhoSite sd).getD j []) x y = (f4 sd.N j x y).headD 0 := by
    intro sd j x y
    simp only [rhoSite, ent, f4]
    rw [getD_map' _ _ _ [] _ (by simp), getD_map' _ _ _ [] _ (by simp), getD_map' _ _ _ [] _ (by simp)]
  show ((NP _ (b.site cuts i).N p) a c).eval 0 = _
  simp only [NP, Matrix.of_apply, eval_toP_zero]
  fin_cases i <;> simp only [rhoE, partRhos, List.getD_cons_zero, List.getD_cons_succ, e] <;> rfl

theorem rhoE_partRhos_qub (cuts : ℕ → CutData) (b : BCode) (n : ℕ) (p : P4)
    (a c : Fin (b.toSpec cuts n).kq) :
    (b.toSpec cuts n).Fq p a c = (rhoE (partRhos cuts b) 3 (permIdx p) a c : ℝ) := rfl

theorem rhoE_rhoMap (m : Fin 24 → Fin 24) (R : List (List (List (List ℤ)))) (i j a c : ℕ) (hj : j < 24) :
    rhoE (R.map (rhoMap m)) i j a c = rhoE R i (m (WernerEndpoint.fin24 j)) a c := by
  have e1 : (R.map (rhoMap m)).getD i [] = (R[i]?.map (rhoMap m)).getD [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have e2 : R.getD i [] = R[i]?.getD [] := List.getD_eq_getElem?_getD
  simp only [rhoE, ent]
  rw [e1, e2]
  cases R[i]? with
  | none => simp
  | some T =>
    have e3 : (rhoMap m T).getD j [] = T.getD (m (WernerEndpoint.fin24 j)) [] := by
      simp only [rhoMap]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      rfl
    simp only [Option.map_some, Option.getD_some, e3]

/-! ### One part -/

theorem basis_mul_apply (k : Fin 3 → ℕ) (kq bb ncol n : ℕ) (Pl Pr : List ℤ) (X : Matrix (Fin n) (Fin n) ℝ)
    (Xint : List (List ℤ)) (c : ℝ) (hc : c ≠ 0) (hX : ∀ p q : Fin n, (ent Xint p q : ℝ) = c * X p q)
    (x y : ((i : Fin 3) → Fin (k i)) × Fin kq) :
    (basisMat k kq bb ncol Pl n * X * (basisMat k kq bb ncol Pr n)ᵀ) x y =
      (Ymat n Xint (Pl.map (unpk bb ncol)) (Pr.map (unpk bb ncol))
        (flatIdx k kq (fun i => x.1 i) x.2) (flatIdx k kq (fun i => y.1 i) y.2) : ℝ) / c := by
  have hX' : ∀ p q : Fin n, X p q = (ent Xint p q : ℝ) / c := fun p q => by
    rw [hX, mul_div_cancel_left₀ _ hc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisMat, Matrix.of_apply, Ymat, hX']
  push_cast
  simp only [Finset.sum_range, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  simp only [g2, ent]
  ring

/-- **One part.** The pairing of `B_l X B_rᵀ` (packed bases `Pl`, `Pr`) with `blockOp N Fq mp m` is
`∑_s m(s) FTP P s / c` for any part data `P` with the block's `ks`, `k`, `X`, `B_l`, `B_r`, `rhos`,
when the tables of `N ∘ mp`, `Fq ∘ mp` are `rhos`. -/
theorem pair_part (k : Fin 3 → ℕ) (kq bb ncol n : ℕ) (N0 : (i : Fin 3) → P4 → Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (Fq : P4 → Matrix (Fin kq) (Fin kq) ℝ) (mp : P4 ≃ P4) (rhos : List (List (List (List ℤ))))
    (hN : ∀ i p a b, N0 i (mp p) a b = (rhoE rhos i (permIdx p) a b : ℝ))
    (hF : ∀ p a b, Fq (mp p) a b = (rhoE rhos 3 (permIdx p) a b : ℝ))
    (Pl Pr : List ℤ) (X : Matrix (Fin n) (Fin n) ℝ) (Xint : List (List ℤ)) (c : ℝ) (hc : c ≠ 0)
    (hX : ∀ p q : Fin n, (ent Xint p q : ℝ) = c * X p q) (P : PartData)
    (hks : P.ks = [k 0, k 1, k 2, kq]) (hk : P.k = n) (hPX : P.X = Xint)
    (hBl : P.Bl = Pl.map (unpk bb ncol)) (hBr : P.Br = Pr.map (unpk bb ncol)) (hrh : P.rhos = rhos)
    (m : Tup (Fin 3) → ℝ) :
    ∑ x, ∑ y, (basisMat k kq bb ncol Pl n * X * (basisMat k kq bb ncol Pr n)ᵀ) x y *
        blockOp N0 Fq mp m x y = ∑ s, m s * (FTP P s : ℝ) / c := by
  have h1 := pair_blockOp (basisMat k kq bb ncol Pl n * X * (basisMat k kq bb ncol Pr n)ᵀ) N0 Fq mp m
  rw [h1]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 := pair_rtens_Fv k kq rhos _ c _ (basis_mul_apply k kq bb ncol n Pl Pr X Xint c hc hX) _ _
    (fun i => permIdx (s.1 i)) (permIdx s.2) (fun i a b => hN i (s.1 i) a b) (fun a b => hF s.2 a b)
  have h3 := FTP_eq P _ _ _ _ hks s
  rw [hk, hPX, hBl, hBr, hrh] at h3
  rw [mul_div_assoc, h3, h2]

/-! ### The bridge: one block -/

section Blocks
variable (cuts : ℕ → CutData) (b : BCode) (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (Xint : List (List ℤ))
  (c : ℝ) (hc : c ≠ 0) (hX : ∀ p q : Fin n, (ent Xint p q : ℝ) = c * X p q)

/-- The `ks` of a block code's parts. -/
def BCode.ks : List ℕ := [(b.site cuts 0).k, (b.site cuts 1).k, (b.site cuts 2).k, (b.qub cuts).k]

theorem rhoE_mapped_site (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) (i : Fin 3) (p : P4)
    (a a' : Fin ((b.toSpec cuts n).k i)) :
    (b.toSpec cuts n).N0 i (mpE m hm p) a a' =
      (rhoE ((partRhos cuts b).map (rhoMap m)) i (permIdx p) a a' : ℝ) := by
  rw [rhoE_partRhos_site, permIdx_mpE, rhoE_rhoMap _ _ _ _ _ _ (permIdx_lt p)]

theorem rhoE_mapped_qub (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) (p : P4)
    (a a' : Fin (b.toSpec cuts n).kq) :
    (b.toSpec cuts n).Fq (mpE m hm p) a a' =
      (rhoE ((partRhos cuts b).map (rhoMap m)) 3 (permIdx p) a a' : ℝ) := by
  rw [rhoE_partRhos_qub, permIdx_mpE, rhoE_rhoMap _ _ _ _ _ _ (permIdx_lt p)]

include hc hX in
/-- **The bridge, word blocks.** `⟨X, L_b(μ)⟩ = ∑_s μ_f(s) FTP P s / c` for any part data `P` carrying the
block's tables, basis and `Xint` (`ent Xint p q = c · X p q`). -/
theorem pair_word {f : Fam} {T : Finset (Fin 4)} (hk : b.kind = .word f T) (P : PartData)
    (hks : P.ks = b.ks cuts) (hkn : P.k = n) (hPX : P.X = Xint) (hBl : P.Bl = basisRows b b.Bp)
    (hBr : P.Br = basisRows b b.Bp) (hrh : P.rhos = partRhos cuts b) (μ : Fam → Tup (Fin 3) → ℝ) :
    ∑ i, ∑ i', X i i' * (b.toSpec cuts n).L μ i i' = ∑ s, μ f s * (FTP P s : ℝ) / c := by
  have hk' : (b.toSpec cuts n).kind = .word f T := hk
  simp only [BlockSpec.L, hk']
  rw [pair_congr]
  exact pair_part (fun i => (b.site cuts i).k) (b.qub cuts).k b.bb b.ncol n (b.toSpec cuts n).N0
    (b.toSpec cuts n).Fq (Equiv.refl _) (partRhos cuts b) (fun i p a a' => rhoE_partRhos_site cuts b n i p a a')
    (fun p a a' => rhoE_partRhos_qub cuts b n p a a') b.Bp b.Bp X Xint c hc hX P hks hkn hPX hBl hBr hrh (μ f)

include hc hX in
/-- The coupled pairing for the maps `m₁, m₂, m₃` (families 31, 22, 13), symmetric `X`. -/
theorem pair_coupledOp (m1 m2 m3 : Fin 24 → Fin 24) (hm1 : ∀ j, ∃ i, m1 i = j) (hm2 : ∀ j, ∃ i, m2 i = j)
    (hm3 : ∀ j, ∃ i, m3 i = j) (hsym : Xᵀ = X) (P31 P22 P13 : PartData)
    (hks : P31.ks = b.ks cuts ∧ P22.ks = b.ks cuts ∧ P13.ks = b.ks cuts)
    (hkn : P31.k = n ∧ P22.k = n ∧ P13.k = n) (hPX : P31.X = Xint ∧ P22.X = Xint ∧ P13.X = Xint)
    (hB : P31.Bl = basisRows b b.Bp ∧ P31.Br = basisRows b b.Bp ∧ P22.Bl = basisRows b b.Bp ∧
      P22.Br = basisRows b b.Bvp ∧ P13.Bl = basisRows b b.Bvp ∧ P13.Br = basisRows b b.Bvp)
    (hrh : P31.rhos = (partRhos cuts b).map (rhoMap m1) ∧ P22.rhos = (partRhos cuts b).map (rhoMap m2) ∧
      P13.rhos = (partRhos cuts b).map (rhoMap m3))
    (μ : Fam → Tup (Fin 3) → ℝ) :
    ∑ i, ∑ i', X i i' * ((fromRows (b.toSpec cuts n).B (b.toSpec cuts n).Bv)ᵀ *
        (b.toSpec cuts n).coupledOp (mpE m1 hm1) (mpE m2 hm2) (mpE m3 hm3) μ *
        fromRows (b.toSpec cuts n).B (b.toSpec cuts n).Bv) i i' =
      ∑ s, μ .f31 s * (FTP P31 s : ℝ) / c + 2 * ∑ s, μ .f22 s * (FTP P22 s : ℝ) / c +
        ∑ s, μ .f13 s * (FTP P13 s : ℝ) / c := by
  rw [BlockSpec.coupledOp, pair_coupled X hsym]
  have part := fun (m : Fin 24 → Fin 24) (hm : ∀ j, ∃ i, m i = j) (Pl Pr : List ℤ) (P : PartData)
      (hks : P.ks = b.ks cuts) (hkn : P.k = n) (hPX : P.X = Xint) (hBl : P.Bl = basisRows b Pl)
      (hBr : P.Br = basisRows b Pr) (hrh : P.rhos = (partRhos cuts b).map (rhoMap m)) (mm : Tup (Fin 3) → ℝ) =>
    pair_part (fun i => (b.site cuts i).k) (b.qub cuts).k b.bb b.ncol n (b.toSpec cuts n).N0
      (b.toSpec cuts n).Fq (mpE m hm) _ (fun i p a a' => rhoE_mapped_site cuts b n m hm i p a a')
      (fun p a a' => rhoE_mapped_qub cuts b n m hm p a a') Pl Pr X Xint c hc hX P hks hkn hPX hBl hBr hrh mm
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ (congrArg (2 * ·) ?_)) ?_
  · exact part m1 hm1 b.Bp b.Bp P31 hks.1 hkn.1 hPX.1 hB.1 hB.2.1 hrh.1 _
  · exact part m2 hm2 b.Bp b.Bvp P22 hks.2.1 hkn.2.1 hPX.2.1 hB.2.2.1 hB.2.2.2.1 hrh.2.1 _
  · exact part m3 hm3 b.Bvp b.Bvp P13 hks.2.2 hkn.2.2 hPX.2.2 hB.2.2.2.2.1 hB.2.2.2.2.2 hrh.2.2 _

include hc hX in
/-- **The bridge, coupled block `{3}`.** -/
theorem pair_c3 (hk : b.kind = .c3) (hsym : Xᵀ = X) (P31 P22 P13 : PartData)
    (hks : P31.ks = b.ks cuts ∧ P22.ks = b.ks cuts ∧ P13.ks = b.ks cuts)
    (hkn : P31.k = n ∧ P22.k = n ∧ P13.k = n) (hPX : P31.X = Xint ∧ P22.X = Xint ∧ P13.X = Xint)
    (hB : P31.Bl = basisRows b b.Bp ∧ P31.Br = basisRows b b.Bp ∧ P22.Bl = basisRows b b.Bp ∧
      P22.Br = basisRows b b.Bvp ∧ P13.Bl = basisRows b b.Bvp ∧ P13.Br = basisRows b b.Bvp)
    (hrh : P31.rhos = (partRhos cuts b).map (rhoMap mT3_31) ∧
      P22.rhos = (partRhos cuts b).map (rhoMap mT3_22) ∧ P13.rhos = (partRhos cuts b).map (rhoMap mT3_13))
    (μ : Fam → Tup (Fin 3) → ℝ) :
    ∑ i, ∑ i', X i i' * (b.toSpec cuts n).L μ i i' =
      ∑ s, μ .f31 s * (FTP P31 s : ℝ) / c + 2 * ∑ s, μ .f22 s * (FTP P22 s : ℝ) / c +
        ∑ s, μ .f13 s * (FTP P13 s : ℝ) / c := by
  have hk' : (b.toSpec cuts n).kind = .c3 := hk
  simp only [BlockSpec.L, hk']
  exact pair_coupledOp cuts b n X Xint c hc hX _ _ _ _ _ _ hsym P31 P22 P13 hks hkn hPX hB hrh μ

include hc hX in
/-- **The bridge, coupled block `{2,3}`.** -/
theorem pair_c23 (hk : b.kind = .c23) (hsym : Xᵀ = X) (P31 P22 P13 : PartData)
    (hks : P31.ks = b.ks cuts ∧ P22.ks = b.ks cuts ∧ P13.ks = b.ks cuts)
    (hkn : P31.k = n ∧ P22.k = n ∧ P13.k = n) (hPX : P31.X = Xint ∧ P22.X = Xint ∧ P13.X = Xint)
    (hB : P31.Bl = basisRows b b.Bp ∧ P31.Br = basisRows b b.Bp ∧ P22.Bl = basisRows b b.Bp ∧
      P22.Br = basisRows b b.Bvp ∧ P13.Bl = basisRows b b.Bvp ∧ P13.Br = basisRows b b.Bvp)
    (hrh : P31.rhos = (partRhos cuts b).map (rhoMap mT23_31) ∧
      P22.rhos = (partRhos cuts b).map (rhoMap mT23_22) ∧ P13.rhos = (partRhos cuts b).map (rhoMap mT23_13))
    (μ : Fam → Tup (Fin 3) → ℝ) :
    ∑ i, ∑ i', X i i' * (b.toSpec cuts n).L μ i i' =
      ∑ s, μ .f31 s * (FTP P31 s : ℝ) / c + 2 * ∑ s, μ .f22 s * (FTP P22 s : ℝ) / c +
        ∑ s, μ .f13 s * (FTP P13 s : ℝ) / c := by
  have hk' : (b.toSpec cuts n).kind = .c23 := hk
  simp only [BlockSpec.L, hk']
  exact pair_coupledOp cuts b n X Xint c hc hX _ _ _ _ _ _ hsym P31 P22 P13 hks hkn hPX hB hrh μ

end Blocks

end LayerDT0

#print axioms LayerDT0.pair_word
#print axioms LayerDT0.pair_c3
#print axioms LayerDT0.pair_c23
