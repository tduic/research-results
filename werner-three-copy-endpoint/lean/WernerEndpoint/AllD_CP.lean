import WernerEndpoint.LayerC_Projection
import Mathlib.LinearAlgebra.Lagrange

/-!
# All-d lemma chain, step 5: module forms are completely positive (the realisation lemma)

The verifier's site modules are integer polynomial matrices `F_r(p)(d)` that satisfy, as
polynomial identities, `F(p)ᵀ = F(p⁻¹)` and `F(p) adj F(e) F(q) = d^{l(p,q)} det F(e) F(s(p,q))`,
with `F(e)` positive definite for `d ≥ 4` (verifier (A2), (A3)). The README states the consequence
as a *realisation* `F_r(p) = κ (JV)ᵀ Γ_T(P_p) (JV)`. What the block positivity actually uses is the
following **complete positivity** statement, proved here abstractly (no realisation vectors, no
Haar measure, no Wedderburn theory):

`cp_of_module`: let `O : P → Matrix V V ℂ` be a family of operators closed under products and
adjoints, `O p O q = c(p,q) O(s(p,q))`, `(O p)ᴴ = O(inv p)`, `O e = 1`, with **dual entries**
(for each `p` an entry where `O p` is `1` and every other `O p'` is `0`; for the partially
transposed diagrams this holds for `d ≥ 4`, `dualEntry_ptrans_sP`). Let `F_i : P → Matrix (K i)`
be modules with a positive semidefinite `H_i` such that
`c(inv p, q) F_i(s(inv p, q)) = F_i(p)ᴴ H_i F_i(q)` (from (A2)–(A3) with `H = F(e)⁻¹`,
`moduleAt_of_verifier`). Then for **every** auxiliary space `W` and coefficient matrices `R_t`,

  `∑_t (⊗_i O(t_i)) ⊗ R_t ⪰ 0   ⟹   ∑_t (⊗_i F_i(t_i)) ⊗ R_t ⪰ 0`.

Proof: the left side lies in the unital `*`-algebra `𝒜 = {∑_t (⊗O(t_i)) ⊗ R_t}`; a PSD element
of `𝒜` is `BᴴB` with `B = p(Z) ∈ 𝒜` for a real polynomial `p` interpolating `√` on the spectrum
(`exists_poly_sqrt`); dual entries make the coefficients `R_t` unique, so the coefficients of
`BᴴB` can be read off; the module relation then turns `∑_t (⊗F(t_i)) ⊗ R_t` into `Kᴴ (⊗H ⊗ 1) K`.

`W` is arbitrary, so the qubit factor (`W = (ℂ²)^{⊗4}`) and the 2×2 coupled blocks
(`W ⊕ W`) are covered by the same statement.
-/

open Matrix Polynomial
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Sqrt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Polynomial square root.** A PSD matrix is `BᴴB` with `B = p(Z)` for a real polynomial `p`. -/
theorem exists_poly_sqrt {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) :
    ∃ p : ℝ[X], (aeval Z p)ᴴ * aeval Z p = Z := by
  have hH : Z.IsHermitian := hZ.isHermitian
  set ev := hH.eigenvalues with hev
  have hev0 : ∀ i, 0 ≤ ev i := hZ.eigenvalues_nonneg
  let s : Finset ℝ := Finset.univ.image ev
  let p : ℝ[X] := Lagrange.interpolate s id (fun x => Real.sqrt x)
  have hp : ∀ i, p.eval (ev i) = Real.sqrt (ev i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (fun x => Real.sqrt x)
      (Set.injOn_id _) (Finset.mem_image_of_mem ev (Finset.mem_univ i))
    simpa using this
  refine ⟨p, ?_⟩
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : star U * U = 1 := unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hsa : IsSelfAdjoint Z := hH
  let dp : n → ℂ := fun i => ((p.eval (ev i) : ℝ) : ℂ)
  have hBeq : aeval Z p = U * diagonal dp * star U := by
    rw [← cfc_polynomial p Z hsa, hH.cfc_eq]
    rfl
  have hZeq : Z = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hdpstar : (diagonal dp)ᴴ = diagonal dp := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [dp]
  rw [hBeq, conjTranspose_conj_unitary, hdpstar, conj_unitary_mul hU, diagonal_mul_diagonal]
  conv_rhs => rw [hZeq]
  congr 3
  funext i
  simp only [dp, hp]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hev0 i)]

end Sqrt

section GTens

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : κ → Type*} [∀ i, Fintype (K i)]
  [∀ i, DecidableEq (K i)] {W : Type*} [Fintype W] [DecidableEq W]
  {K' K'' : κ → Type*} [∀ i, Fintype (K' i)] {W' W'' : Type*} [Fintype W']

/-- `(⊗_i A_i) ⊗ S` on `(∏_i K_i) × W` (rectangular factors allowed). -/
def gtens (A : (i : κ) → Matrix (K i) (K' i) ℂ) (S : Matrix W W' ℂ) :
    Matrix (((i : κ) → K i) × W) (((i : κ) → K' i) × W') ℂ :=
  Matrix.of fun X Y => (∏ i, A i (X.1 i) (Y.1 i)) * S X.2 Y.2

theorem gtens_mul (A : (i : κ) → Matrix (K i) (K' i) ℂ) (A' : (i : κ) → Matrix (K' i) (K'' i) ℂ)
    (S : Matrix W W' ℂ) (S' : Matrix W' W'' ℂ) :
    gtens A S * gtens A' S' = gtens (fun i => A i * A' i) (S * S') := by
  ext X Z
  simp only [gtens, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  have h : ∀ y : (i : κ) → K' i, ∀ w : W',
      (∏ i, A i (X.1 i) (y i)) * S X.2 w * ((∏ i, A' i (y i) (Z.1 i)) * S' w Z.2) =
        (∏ i, A i (X.1 i) (y i) * A' i (y i) (Z.1 i)) * (S X.2 w * S' w Z.2) := by
    intro y w; rw [Finset.prod_mul_distrib]; ring
  simp only [h, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun i j => A i (X.1 i) j * A' i j (Z.1 i))).symm

theorem gtens_conjTranspose (A : (i : κ) → Matrix (K i) (K' i) ℂ) (S : Matrix W W' ℂ) :
    (gtens A S)ᴴ = gtens (fun i => (A i)ᴴ) Sᴴ := by
  ext X Y
  simp only [gtens, conjTranspose_apply, Matrix.of_apply, star_mul', star_prod]

theorem gtens_one : gtens (K := K) (K' := K) (W := W) (W' := W) (fun _ => 1) 1 = 1 := by
  ext X Y
  simp only [gtens, Matrix.of_apply, Matrix.one_apply]
  by_cases h : X = Y
  · subst h; simp
  · rw [if_neg h]
    by_cases h2 : X.2 = Y.2
    · have : ∃ i, X.1 i ≠ Y.1 i := by
        by_contra hc; push_neg at hc
        exact h (Prod.ext (funext hc) h2)
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_mul]
    · rw [if_neg h2, mul_zero]

theorem gtens_zero (A : (i : κ) → Matrix (K i) (K' i) ℂ) : gtens A (0 : Matrix W W' ℂ) = 0 := by
  ext X Y; simp [gtens]

theorem gtens_smul (A : (i : κ) → Matrix (K i) (K' i) ℂ) (a : ℂ) (S : Matrix W W' ℂ) :
    gtens A (a • S) = a • gtens A S := by
  ext X Y; simp only [gtens, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; ring

theorem gtens_sum {β : Type*} (A : (i : κ) → Matrix (K i) (K' i) ℂ) (s : Finset β)
    (S : β → Matrix W W' ℂ) : gtens A (∑ b ∈ s, S b) = ∑ b ∈ s, gtens A (S b) := by
  ext X Y; simp only [gtens, Matrix.of_apply, Matrix.sum_apply, Finset.mul_sum]

theorem gtens_smul_left (A : (i : κ) → Matrix (K i) (K' i) ℂ) (a : κ → ℂ) (S : Matrix W W' ℂ) :
    gtens (fun i => a i • A i) S = (∏ i, a i) • gtens A S := by
  ext X Y
  simp only [gtens, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  ring

/-- Regrouping a double sum by the value of an index map. -/
theorem regroup {β : Type*} [Fintype β] {U : Type*} [Fintype U] [DecidableEq U]
    (G : U → Matrix W W ℂ → Matrix (((i : κ) → K i) × W) (((i : κ) → K i) × W) ℂ)
    (hG0 : ∀ u, G u 0 = 0) (hGs : ∀ u (S : β → Matrix W W ℂ), G u (∑ b, S b) = ∑ b, G u (S b))
    (σ : β → U) (X : β → Matrix W W ℂ) :
    ∑ u, G u (∑ b, if σ b = u then X b else 0) = ∑ b, G (σ b) (X b) := by
  simp only [hGs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∀ u, G u (if σ b = u then X b else 0) = if σ b = u then G (σ b) (X b) else 0 := by
    intro u; split_ifs with h
    · rw [h]
    · exact hG0 u
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem posSemidef_sum {n β : Type*} [Fintype n] (s : Finset β) {M : β → Matrix n n ℂ}
    (h : ∀ b, (M b).PosSemidef) : (∑ b ∈ s, M b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert x s hx ih => rw [Finset.sum_insert hx]; exact (h x).add ih

end GTens

section CP

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {V : Type*} [Fintype V] [DecidableEq V]
  {P : Type*} [Fintype P] [DecidableEq P] {W : Type*} [Fintype W] [DecidableEq W]

/-- A family of operators closed under products and adjoints, containing `1`, with dual
entries (so linearly independent, with entrywise-readable coefficients). -/
structure DiagFamily (O : P → Matrix V V ℂ) (s : P → P → P) (c : P → P → ℂ) (inv : P → P)
    (e : P) : Prop where
  mul : ∀ p q, O p * O q = c p q • O (s p q)
  star : ∀ p, (O p)ᴴ = O (inv p)
  one : O e = 1
  dual : ∀ p, ∃ x y, ∀ p', O p' x y = if p' = p then 1 else 0

variable {O : P → Matrix V V ℂ} {s : P → P → P} {c : P → P → ℂ} {inv : P → P} {e : P}

/-- `(⊗_i O(t_i)) ⊗ S`. -/
abbrev tensO (O : P → Matrix V V ℂ) (t : κ → P) (S : Matrix W W ℂ) :=
  gtens (K := fun _ : κ => V) (K' := fun _ : κ => V) (fun i => O (t i)) S

/-- The algebra `{∑_t (⊗O(t_i)) ⊗ R_t}`. -/
def decAlg (O : P → Matrix V V ℂ) : Submodule ℂ (Matrix ((κ → V) × W) ((κ → V) × W) ℂ) where
  carrier := {M | ∃ R : (κ → P) → Matrix W W ℂ, M = ∑ t, tensO O t (R t)}
  add_mem' := by
    rintro M N ⟨R, rfl⟩ ⟨R', rfl⟩
    refine ⟨fun t => R t + R' t, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ext X Y; simp [gtens, mul_add]
  zero_mem' := ⟨fun _ => 0, by simp [gtens_zero]⟩
  smul_mem' := by
    rintro a M ⟨R, rfl⟩
    exact ⟨fun t => a • R t, by simp only [gtens_smul, Finset.smul_sum]⟩

theorem tensO_mem (u : κ → P) (S : Matrix W W ℂ) : tensO O u S ∈ decAlg (κ := κ) (W := W) O := by
  refine ⟨fun t => if t = u then S else 0, ?_⟩
  have : ∀ t, tensO O t (if t = u then S else 0) = if t = u then tensO O u S else 0 := by
    intro t; split_ifs with h
    · rw [h]
    · exact gtens_zero _
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_mem_decAlg {β : Type*} (S : Finset β) {M : β → Matrix ((κ → V) × W) ((κ → V) × W) ℂ}
    (h : ∀ b, M b ∈ decAlg (κ := κ) (W := W) O) : ∑ b ∈ S, M b ∈ decAlg (κ := κ) (W := W) O :=
  Submodule.sum_mem _ fun b _ => h b

theorem tensO_mul (hO : DiagFamily O s c inv e) (t t' : κ → P) (S S' : Matrix W W ℂ) :
    tensO O t S * tensO O t' S' =
      (∏ i, c (t i) (t' i)) • tensO O (fun i => s (t i) (t' i)) (S * S') := by
  rw [gtens_mul]
  simp only [hO.mul]
  rw [gtens_smul_left (K := fun _ : κ => V) (fun i => O (s (t i) (t' i)))]

theorem tensO_conjTranspose (hO : DiagFamily O s c inv e) (t : κ → P) (S : Matrix W W ℂ) :
    (tensO O t S)ᴴ = tensO O (fun i => inv (t i)) Sᴴ := by
  rw [gtens_conjTranspose]
  simp only [hO.star]

theorem isStarAlg_decAlg (hO : DiagFamily O s c inv e) :
    IsStarAlg (decAlg (κ := κ) (W := W) O) where
  one_mem := by
    have h1 : tensO (κ := κ) (W := W) O (fun _ => e) 1 = 1 := by
      show gtens (fun _ => O e) 1 = 1
      rw [hO.one]; exact gtens_one
    rw [← h1]; exact tensO_mem _ _
  mul_mem := by
    rintro M N ⟨R, rfl⟩ ⟨R', rfl⟩
    rw [Finset.sum_mul]
    refine sum_mem_decAlg _ fun t => ?_
    rw [Finset.mul_sum]
    refine sum_mem_decAlg _ fun t' => ?_
    rw [tensO_mul hO]
    exact Submodule.smul_mem _ _ (tensO_mem _ _)
  star_mem := by
    rintro M ⟨R, rfl⟩
    rw [conjTranspose_sum]
    refine sum_mem_decAlg _ fun t => ?_
    rw [tensO_conjTranspose hO]
    exact tensO_mem _ _

/-- **Uniqueness of coefficients** (dual entries). -/
theorem coeff_unique (hO : DiagFamily O s c inv e) {R R' : (κ → P) → Matrix W W ℂ}
    (h : ∑ t, tensO O t (R t) = ∑ t, tensO O t (R' t)) : R = R' := by
  choose x y hxy using hO.dual
  funext t
  ext w w'
  have := congrFun (congrFun h (fun i => x (t i), w)) (fun i => y (t i), w')
  simp only [Matrix.sum_apply, gtens, Matrix.of_apply, hxy] at this
  have hp : ∀ t' : κ → P, (∏ i, if t' i = t i then (1 : ℂ) else 0) = if t' = t then 1 else 0 := by
    intro t'
    rw [Fintype.prod_boole]
    congr 1
    exact propext ⟨fun h => funext h, fun h i => by rw [h]⟩
  simp only [hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    at this
  exact this

/-- **Complete positivity of a module** (the abstract realisation lemma; see the module doc). -/
theorem cp_of_module (hO : DiagFamily O s c inv e) {K : κ → Type*} [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (F : (i : κ) → P → Matrix (K i) (K i) ℂ)
    (H : (i : κ) → Matrix (K i) (K i) ℂ) (hH : ∀ i, (H i).PosSemidef)
    (hmod : ∀ i p q, c (inv p) q • F i (s (inv p) q) = (F i p)ᴴ * H i * F i q)
    (R : (κ → P) → Matrix W W ℂ) (hR : (∑ t, tensO O t (R t)).PosSemidef) :
    (∑ t, gtens (fun i => F i (t i)) (R t)).PosSemidef := by
  set Z := ∑ t, tensO O t (R t) with hZdef
  have hZmem : Z ∈ decAlg (κ := κ) (W := W) O := ⟨R, rfl⟩
  obtain ⟨p, hp⟩ := exists_poly_sqrt hR
  obtain ⟨S, hS⟩ := aeval_mem (isStarAlg_decAlg hO) hZmem p
  set B := aeval Z p
  -- coefficients of `BᴴB`
  let a : (κ → P) × (κ → P) → ℂ := fun pq => ∏ i, c (inv (pq.1 i)) (pq.2 i)
  let σ : (κ → P) × (κ → P) → (κ → P) := fun pq i => s (inv (pq.1 i)) (pq.2 i)
  let X : (κ → P) × (κ → P) → Matrix W W ℂ := fun pq => a pq • ((S pq.1)ᴴ * S pq.2)
  have hBB : Bᴴ * B = ∑ pq : (κ → P) × (κ → P), tensO O (σ pq) (X pq) := by
    rw [hS, conjTranspose_sum, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t' _ => ?_
    simp only [X, a, σ]
    rw [tensO_conjTranspose hO, tensO_mul hO]
    exact (gtens_smul _ _ _).symm
  have hG0 : ∀ u : κ → P, tensO (W := W) O u 0 = 0 := fun u => gtens_zero _
  have hGs : ∀ (u : κ → P) (M : (κ → P) × (κ → P) → Matrix W W ℂ),
      tensO O u (∑ b, M b) = ∑ b, tensO O u (M b) := fun u M => gtens_sum _ _ _
  have hRR : R = fun u => ∑ pq, if σ pq = u then X pq else 0 := by
    apply coeff_unique hO
    rw [← hZdef, ← hp, hBB, regroup (fun u M => tensO O u M) hG0 hGs σ X]
  -- the target in terms of `S`
  have hF0 : ∀ u : κ → P, gtens (W := W) (W' := W) (fun i => F i (u i)) 0 = 0 := fun u => gtens_zero _
  have hFs : ∀ (u : κ → P) (M : (κ → P) × (κ → P) → Matrix W W ℂ),
      gtens (fun i => F i (u i)) (∑ b, M b) = ∑ b, gtens (fun i => F i (u i)) (M b) :=
    fun u M => gtens_sum _ _ _
  rw [hRR, regroup (fun u M => gtens (fun i => F i (u i)) M) hF0 hFs σ X]
  -- `∑_{p,q} (⊗ F(p)ᴴ H F(q)) ⊗ S_pᴴ S_q = Kᴴ (⊗H ⊗ 1) K`
  let L : (i : κ) → Matrix (K i) (K i) ℂ := fun i => aeval (H i) (Classical.choose
    (exists_poly_sqrt (hH i)))
  have hL : ∀ i, (L i)ᴴ * L i = H i := fun i => Classical.choose_spec (exists_poly_sqrt (hH i))
  let Kop := ∑ q : κ → P, gtens (fun i => F i (q i)) (S q)
  have key : ∑ pq : (κ → P) × (κ → P), gtens (fun i => F i (σ pq i)) (X pq) =
      (gtens L 1 * Kop)ᴴ * (gtens L 1 * Kop) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gtens L 1)ᴴ, gtens_conjTranspose,
      gtens_mul, conjTranspose_one, Matrix.one_mul]
    simp only [hL]
    simp only [Kop, conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    simp only [X, a, σ]
    rw [gtens_smul, ← gtens_smul_left (K := K) (fun i => F i (s (inv (t i)) (t' i)))]
    simp only [hmod]
    rw [gtens_conjTranspose, gtens_mul, gtens_mul]
    simp only [Matrix.mul_assoc, Matrix.one_mul]
  rw [key]
  exact posSemidef_conjTranspose_mul_self _

end CP

end WernerEndpoint

end

#print axioms WernerEndpoint.exists_poly_sqrt
#print axioms WernerEndpoint.gtens_mul
#print axioms WernerEndpoint.gtens_one
#print axioms WernerEndpoint.regroup
#print axioms WernerEndpoint.isStarAlg_decAlg
#print axioms WernerEndpoint.coeff_unique
#print axioms WernerEndpoint.cp_of_module
