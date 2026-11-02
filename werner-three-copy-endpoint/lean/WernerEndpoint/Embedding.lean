import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.Embedding
import WernerEndpoint.L1_Swap
import WernerEndpoint.L4_WordPositivity

/-!
# The embedding lemma: the endpoint at local dimension `D` implies it at every `d ≤ D`

Let `V : Matrix ι' ι ℂ` be an isometry (`Vᴴ * V = 1`). For an operator `C` on `(κ → ι)` (sites `κ`,
later `Fin 3`; local space `ι`, later `Fin d`) the *embedded* operator on `(κ → ι')` is

  `embedOp V C = (⊗_κ V) C (⊗_κ V)ᴴ`,

with `V` applied at every site (`tpow κ V = ⊗_κ V`, the rectangular analogue of `prodOp`).

* `rank_embedOp`: `rank (embedOp V C) = rank C` (in particular `rank_embedOp_le`: rank `≤ 2` is
  preserved).
* `partialTrace_embedOp` (**key lemma**): `Tr_S (embedOp V C) = embedOp V (Tr_S C)`, i.e.
  `Tr_S ((⊗_κ V) C (⊗_κ V)ᴴ) = (⊗_{κ∖S} V) (Tr_S C) (⊗_{κ∖S} V)ᴴ`.
* `frobSq_conj_of_isometry`: `‖A M Aᴴ‖²_F = ‖M‖²_F` for every isometry `A`.
* `qfun_embedOp`: `q(embedOp V C) = q(C)`.
* `isoOfEmb f` is the isometry of an injection `f : ι ↪ ι'` (`e_j ↦ e_{f j}`, padding with zeros);
  `embedOp_isoOfEmb_apply_comp` and `embedOp_isoOfEmb_apply_of_left/right` show that
  `embedOp (isoOfEmb f) C` is `C` on the image of `f` and `0` elsewhere.
* Corollaries: `qfun_nonneg_of_isometry`, `qfun_nonneg_of_embedding`, `qfun_nonneg_of_larger`
  (the endpoint at `Fin D` implies it at every `Fin d`, `d ≤ D`) and
  `qfun_nonneg_all_of_unbounded` (if it holds at arbitrarily large `D`, it holds at every `d`).
  They are stated for any finite site type `κ`; the three-copy case is `κ = Fin 3`.
-/

open Matrix

noncomputable section

namespace WernerEndpoint

section TensorPower

variable {α β γ : Type*} {R : Type*} [CommRing R] [StarRing R]

/-- The tensor power `⊗_{r ∈ s} A` of a (possibly rectangular) matrix `A`:
`(tpow s A) x y = ∏ r, A (x r) (y r)`. -/
def tpow (s : Type*) [Fintype s] (A : Matrix α β R) : Matrix (s → α) (s → β) R :=
  Matrix.of fun x y => ∏ r, A (x r) (y r)

omit [StarRing R] in
theorem tpow_apply (s : Type*) [Fintype s] (A : Matrix α β R) (x : s → α) (y : s → β) :
    tpow s A x y = ∏ r, A (x r) (y r) := rfl

omit [StarRing R] in
/-- For a square matrix, `tpow` is the product operator `prodOp` of L4 with constant factors. -/
theorem tpow_eq_prodOp (s : Type*) [Fintype s] (A : Matrix α α R) :
    tpow s A = prodOp (fun _ : s => A) := rfl

omit [StarRing R] in
theorem tpow_mul (s : Type*) [Fintype s] [DecidableEq s] [Fintype β] (A : Matrix α β R)
    (B : Matrix β γ R) : tpow s A * tpow s B = tpow s (A * B) := by
  ext x y
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem tpow_conjTranspose (s : Type*) [Fintype s] (A : Matrix α β R) :
    (tpow s A)ᴴ = tpow s Aᴴ := by
  ext x y
  simp only [tpow, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

omit [StarRing R] in
theorem tpow_one (s : Type*) [Fintype s] [DecidableEq α] :
    tpow s (1 : Matrix α α R) = 1 := by
  ext x y
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨r, hr⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr)

/-- The tensor power of an isometry is an isometry. -/
theorem tpow_isometry (s : Type*) [Fintype s] [DecidableEq s] [Fintype α] [DecidableEq β]
    {V : Matrix α β R} (hV : Vᴴ * V = 1) : (tpow s V)ᴴ * tpow s V = 1 := by
  rw [tpow_conjTranspose, tpow_mul, hV, tpow_one]

end TensorPower

section Conjugation

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
theorem conj_apply {p q : Type*} [Fintype p] (A : Matrix m n ℂ) (C : Matrix n p ℂ)
    (B : Matrix q p ℂ) (x : m) (y : q) :
    (A * C * Bᴴ) x y = ∑ a, ∑ b, A x a * C a b * star (B y b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem rank_conj_le (A : Matrix m n ℂ) (C : Matrix n n ℂ) : (A * C * Aᴴ).rank ≤ C.rank :=
  (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- Conjugation by an isometry preserves the rank. -/
theorem rank_conj_of_isometry [DecidableEq n] {A : Matrix m n ℂ} (hA : Aᴴ * A = 1)
    (C : Matrix n n ℂ) : (A * C * Aᴴ).rank = C.rank := by
  refine le_antisymm (rank_conj_le A C) ?_
  have h : C = Aᴴ * (A * C * Aᴴ) * Aᴴᴴ := by
    rw [conjTranspose_conjTranspose]
    simp only [← Matrix.mul_assoc, hA, Matrix.one_mul]
    rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  calc C.rank = (Aᴴ * (A * C * Aᴴ) * Aᴴᴴ).rank := congrArg Matrix.rank h
    _ ≤ (A * C * Aᴴ).rank := rank_conj_le _ _

/-- `‖M‖²_F = Tr(Mᴴ M)`. -/
theorem ofReal_frobSq_eq_trace (M : Matrix m n ℂ) : ((frobSq M : ℝ) : ℂ) = (Mᴴ * M).trace := by
  rw [ofReal_frobSq, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **Frobenius invariance.** `‖A M Aᴴ‖²_F = ‖M‖²_F` for every isometry `A` (`Aᴴ A = 1`). -/
theorem frobSq_conj_of_isometry [DecidableEq n] {A : Matrix m n ℂ} (hA : Aᴴ * A = 1)
    (M : Matrix n n ℂ) : frobSq (A * M * Aᴴ) = frobSq M := by
  have h : ((frobSq (A * M * Aᴴ) : ℝ) : ℂ) = ((frobSq M : ℝ) : ℂ) := by
    rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace]
    have e : (A * M * Aᴴ)ᴴ * (A * M * Aᴴ) = A * (Mᴴ * M) * Aᴴ := by
      simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Aᴴ A, hA, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, Matrix.one_mul]
  exact_mod_cast h

end Conjugation

section Embedding

variable {κ ι ι' : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι']

/-- The embedded operator `C' = (⊗_κ V) C (⊗_κ V)ᴴ` on `κ → ι'`. -/
def embedOp (V : Matrix ι' ι ℂ) (C : Matrix (κ → ι) (κ → ι) ℂ) : Matrix (κ → ι') (κ → ι') ℂ :=
  tpow κ V * C * (tpow κ V)ᴴ

omit [DecidableEq ι] [DecidableEq ι'] in
/-- **(a)** `rank C' ≤ rank C` (any `V`). -/
theorem rank_embedOp_le (V : Matrix ι' ι ℂ) (C : Matrix (κ → ι) (κ → ι) ℂ) :
    (embedOp V C).rank ≤ C.rank :=
  rank_conj_le _ _

omit [DecidableEq ι'] in
/-- For an isometry `V` the rank is unchanged. -/
theorem rank_embedOp (V : Matrix ι' ι ℂ) (hV : Vᴴ * V = 1) (C : Matrix (κ → ι) (κ → ι) ℂ) :
    (embedOp V C).rank = C.rank :=
  rank_conj_of_isometry (tpow_isometry κ hV) C

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- The tensor power splits over `S` and its complement. -/
theorem tpow_merge (S : Finset κ) (V : Matrix ι' ι ℂ) (u : {r // r ∉ S} → ι')
    (z : {r // r ∈ S} → ι') (u₁ : {r // r ∉ S} → ι) (z₁ : {r // r ∈ S} → ι) :
    tpow κ V (merge S u z) (merge S u₁ z₁) =
      tpow {r // r ∉ S} V u u₁ * tpow {r // r ∈ S} V z z₁ := by
  simp only [tpow, Matrix.of_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun r => r ∈ S), mul_comm]
  congr 1
  · exact Finset.prod_congr (by congr 1) fun r _ => by simp [merge, r.2]
  · exact Finset.prod_congr (by congr 1; exact Subsingleton.elim _ _) fun r _ => by simp [merge, r.2]

omit [DecidableEq ι'] in
/-- **Key lemma.** `Tr_S ((⊗_κ V) C (⊗_κ V)ᴴ) = (⊗_{κ∖S} V) (Tr_S C) (⊗_{κ∖S} V)ᴴ` for an isometry
`V`. -/
theorem partialTrace_embedOp (S : Finset κ) (V : Matrix ι' ι ℂ) (hV : Vᴴ * V = 1)
    (C : Matrix (κ → ι) (κ → ι) ℂ) :
    partialTrace S (embedOp V C) = embedOp V (partialTrace S C) := by
  ext u v
  have hs : ∀ z₁ z₂ : {r // r ∈ S} → ι,
      ∑ z' : {r // r ∈ S} → ι', tpow {r // r ∈ S} V z' z₁ * star (tpow {r // r ∈ S} V z' z₂) =
        if z₁ = z₂ then 1 else 0 := by
    intro z₁ z₂
    have h := congrFun (congrFun (tpow_isometry {r // r ∈ S} hV) z₂) z₁
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply] at h
    rw [eq_comm] at h ⊢
    by_cases hz : z₁ = z₂
    · subst hz
      rw [if_pos rfl] at h ⊢
      rw [h]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · rw [if_neg (Ne.symm hz)] at h
      rw [if_neg hz, h]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have step : ∀ z' : {r // r ∈ S} → ι',
      ∑ a, ∑ b, tpow κ V (merge S u z') a * C a b * star (tpow κ V (merge S v z') b) =
        ∑ u₁, ∑ z₁, ∑ v₁, ∑ z₂, tpow {r // r ∉ S} V u u₁ * tpow {r // r ∈ S} V z' z₁ *
          C (merge S u₁ z₁) (merge S v₁ z₂) *
          star (tpow {r // r ∉ S} V v v₁ * tpow {r // r ∈ S} V z' z₂) := by
    intro z'
    rw [sum_merge S]
    refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun z₁ _ => ?_
    rw [sum_merge S]
    refine Finset.sum_congr rfl fun v₁ _ => Finset.sum_congr rfl fun z₂ _ => ?_
    rw [tpow_merge, tpow_merge]
  simp only [partialTrace, embedOp, Matrix.of_apply, conj_apply]
  calc ∑ z', ∑ a, ∑ b, tpow κ V (merge S u z') a * C a b * star (tpow κ V (merge S v z') b)
      = ∑ z', ∑ u₁, ∑ z₁, ∑ v₁, ∑ z₂, tpow {r // r ∉ S} V u u₁ * tpow {r // r ∈ S} V z' z₁ *
          C (merge S u₁ z₁) (merge S v₁ z₂) *
          star (tpow {r // r ∉ S} V v v₁ * tpow {r // r ∈ S} V z' z₂) :=
        Finset.sum_congr rfl fun z' _ => step z'
    _ = ∑ u₁, ∑ z₁, ∑ v₁, ∑ z₂, tpow {r // r ∉ S} V u u₁ * C (merge S u₁ z₁) (merge S v₁ z₂) *
          star (tpow {r // r ∉ S} V v v₁) * (if z₁ = z₂ then 1 else 0) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u₁ _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun z₁ _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v₁ _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun z₂ _ => ?_
        rw [← hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [star_mul']
        ring
    _ = ∑ u₁, ∑ v₁, ∑ z, tpow {r // r ∉ S} V u u₁ * C (merge S u₁ z) (merge S v₁ z) *
          star (tpow {r // r ∉ S} V v v₁) := by
        refine Finset.sum_congr rfl fun u₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v₁ _ => Finset.sum_congr rfl fun z₁ _ => ?_
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = ∑ u₁, ∑ v₁, tpow {r // r ∉ S} V u u₁ *
          (∑ z, C (merge S u₁ z) (merge S v₁ z)) * star (tpow {r // r ∉ S} V v v₁) := by
        refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun v₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

omit [DecidableEq ι'] in
/-- **(b)** `q(C') = q(C)` for an isometry `V`. -/
theorem qfun_embedOp (V : Matrix ι' ι ℂ) (hV : Vᴴ * V = 1) (C : Matrix (κ → ι) (κ → ι) ℂ) :
    qfun (embedOp V C) = qfun C := by
  unfold qfun
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [partialTrace_embedOp S V hV C, embedOp, frobSq_conj_of_isometry (tpow_isometry _ hV)]

/-- The isometry `ℂ^ι → ℂ^ι'` of an injection `f : ι ↪ ι'`, `e_j ↦ e_{f j}` (padding with
zeros). -/
def isoOfEmb (f : ι ↪ ι') : Matrix ι' ι ℂ :=
  Matrix.of fun i j => if i = f j then 1 else 0

omit [Fintype ι] in
theorem isoOfEmb_isometry (f : ι ↪ ι') : (isoOfEmb f)ᴴ * isoOfEmb f = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, isoOfEmb, Matrix.of_apply,
    Matrix.one_apply]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, f.injective.eq_iff]

omit [DecidableEq κ] [Fintype ι] [DecidableEq ι] [Fintype ι'] in
theorem tpow_isoOfEmb_apply (f : ι ↪ ι') (x : κ → ι') (a : κ → ι) :
    tpow κ (isoOfEmb f) x a = if x = f ∘ a then 1 else 0 := by
  simp only [tpow, isoOfEmb, Matrix.of_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, funext_iff, Function.comp_apply]

omit [Fintype ι'] in
/-- On the image of `f`, the embedded operator is `C`. -/
theorem embedOp_isoOfEmb_apply_comp (f : ι ↪ ι') (C : Matrix (κ → ι) (κ → ι) ℂ)
    (x y : κ → ι) : embedOp (isoOfEmb f) C (f ∘ x) (f ∘ y) = C x y := by
  have hinj : Function.Injective fun a : κ → ι => f ∘ a := f.injective.comp_left
  simp only [embedOp, conj_apply, tpow_isoOfEmb_apply, hinj.eq_iff, apply_ite star, star_one,
    star_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
  simp [Finset.sum_ite_eq]

omit [DecidableEq ι] [Fintype ι'] in
/-- Off the image of `f` (row), the embedded operator vanishes. -/
theorem embedOp_isoOfEmb_apply_of_left (f : ι ↪ ι') (C : Matrix (κ → ι) (κ → ι) ℂ)
    (x y : κ → ι') (hx : ∀ a : κ → ι, x ≠ f ∘ a) : embedOp (isoOfEmb f) C x y = 0 := by
  simp only [embedOp, conj_apply, tpow_isoOfEmb_apply, hx, if_false, zero_mul,
    Finset.sum_const_zero]

omit [DecidableEq ι] [Fintype ι'] in
/-- Off the image of `f` (column), the embedded operator vanishes. -/
theorem embedOp_isoOfEmb_apply_of_right (f : ι ↪ ι') (C : Matrix (κ → ι) (κ → ι) ℂ)
    (x y : κ → ι') (hy : ∀ b : κ → ι, y ≠ f ∘ b) : embedOp (isoOfEmb f) C x y = 0 := by
  simp only [embedOp, conj_apply, tpow_isoOfEmb_apply, hy, if_false, star_zero, mul_zero,
    Finset.sum_const_zero]

omit [DecidableEq ι'] in
/-- If `q ≥ 0` on every rank-`≤ 2` operator on `κ → ι'` and `ι` embeds isometrically in `ι'`,
then `q ≥ 0` on every rank-`≤ 2` operator on `κ → ι`. -/
theorem qfun_nonneg_of_isometry (V : Matrix ι' ι ℂ) (hV : Vᴴ * V = 1)
    (h : ∀ C' : Matrix (κ → ι') (κ → ι') ℂ, C'.rank ≤ 2 → 0 ≤ qfun C')
    (C : Matrix (κ → ι) (κ → ι) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  rw [← qfun_embedOp V hV C]
  exact h _ ((rank_embedOp_le V C).trans hC)

/-- The same for an injection `ι ↪ ι'`. -/
theorem qfun_nonneg_of_embedding (f : ι ↪ ι')
    (h : ∀ C' : Matrix (κ → ι') (κ → ι') ℂ, C'.rank ≤ 2 → 0 ≤ qfun C')
    (C : Matrix (κ → ι) (κ → ι) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C :=
  qfun_nonneg_of_isometry (isoOfEmb f) (isoOfEmb_isometry f) h C hC

end Embedding

section Corollaries

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Monotonicity in the local dimension.** If `0 ≤ q(C)` for every rank-`≤ 2` `C` on
`κ → Fin D`, then the same holds on `κ → Fin d` for every `d ≤ D` (three copies: `κ = Fin 3`). -/
theorem qfun_nonneg_of_larger {d D : ℕ} (hdD : d ≤ D)
    (h : ∀ C : Matrix (κ → Fin D) (κ → Fin D) ℂ, C.rank ≤ 2 → 0 ≤ qfun C)
    (C : Matrix (κ → Fin d) (κ → Fin d) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C :=
  qfun_nonneg_of_embedding (Fin.castLEEmb hdD) h C hC

/-- If the endpoint holds at arbitrarily large local dimension `D`, it holds at every `d`. -/
theorem qfun_nonneg_all_of_unbounded
    (h : ∀ n : ℕ, ∃ D, n ≤ D ∧ ∀ C : Matrix (κ → Fin D) (κ → Fin D) ℂ, C.rank ≤ 2 → 0 ≤ qfun C)
    (d : ℕ) (C : Matrix (κ → Fin d) (κ → Fin d) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  obtain ⟨D, hdD, hD⟩ := h d
  exact qfun_nonneg_of_larger hdD hD C hC

end Corollaries

end WernerEndpoint

end

#print axioms WernerEndpoint.tpow_mul
#print axioms WernerEndpoint.tpow_conjTranspose
#print axioms WernerEndpoint.tpow_one
#print axioms WernerEndpoint.tpow_isometry
#print axioms WernerEndpoint.rank_conj_of_isometry
#print axioms WernerEndpoint.frobSq_conj_of_isometry
#print axioms WernerEndpoint.rank_embedOp_le
#print axioms WernerEndpoint.rank_embedOp
#print axioms WernerEndpoint.tpow_merge
#print axioms WernerEndpoint.partialTrace_embedOp
#print axioms WernerEndpoint.qfun_embedOp
#print axioms WernerEndpoint.isoOfEmb_isometry
#print axioms WernerEndpoint.embedOp_isoOfEmb_apply_comp
#print axioms WernerEndpoint.embedOp_isoOfEmb_apply_of_left
#print axioms WernerEndpoint.embedOp_isoOfEmb_apply_of_right
#print axioms WernerEndpoint.qfun_nonneg_of_isometry
#print axioms WernerEndpoint.qfun_nonneg_of_embedding
#print axioms WernerEndpoint.qfun_nonneg_of_larger
#print axioms WernerEndpoint.qfun_nonneg_all_of_unbounded
