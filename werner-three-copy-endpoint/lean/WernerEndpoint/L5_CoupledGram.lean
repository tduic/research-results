import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Star.BigOperators
import WernerEndpoint.L4_WordPositivity

/-!
# L5: coupled Gram blocks (layer A of `exact_certificate_d5/LEAN_PLAN.md`)

Abstract part of L5. The concrete index tables (the six literal rearrangements of `Y31`, `Y13`,
`Y22` for `T = {3}` and `T = {2,3}`) are left to the data layer; here we prove

* `rearr_vecMulVec_prodVec`: a *literal index rearrangement* of a rank-one product operator is the
  rank-one operator of rearranged (and partly conjugated) product vectors. A rearrangement of an
  operator on `n` copies (`κ` indexes the copies, `ι` a single copy) is given by a bijection
  `σ` of the `2n` digit slots (`Sum.inl s` = row digit of copy `s`, `Sum.inr s` = column digit):
  `rearr σ A x y = A (s ↦ z (σ (inl s))) (s ↦ z (σ (inr s)))` with `z = Sum.elim x y`.
  This is exactly the `einsum` rule of `literal_map` in `verify_d5.py`.
* `fromBlocks_vecMulVec`, `coupled_gram_posSemidef`: `[[u u*, u v*], [v u*, v v*]] = |u⊕v⟩⟨u⊕v| ⪰ 0`.
* `coupled_congr_posSemidef`: for any PSD block matrix `[[A, B], [C, D]]` and any `Bu`, `Bv`,
  `Buᴴ A Bu + Buᴴ B Bv + Bvᴴ C Bu + Bvᴴ D Bv ⪰ 0` (the coupled block compressed by the integer
  bases `Bu`, `Bv`; in the real symmetric case the two cross terms give the verifier's factor 2).
-/

open Matrix

namespace WernerEndpoint

section Gram

variable {R : Type*} [CommRing R] [StarRing R] {n m : Type*}

/-- `[[u u*, u v*], [v u*, v v*]] = |u ⊕ v⟩⟨u ⊕ v|`. -/
theorem fromBlocks_vecMulVec (u : n → R) (v : m → R) :
    fromBlocks (vecMulVec u (star u)) (vecMulVec u (star v)) (vecMulVec v (star u))
        (vecMulVec v (star v)) =
      vecMulVec (Sum.elim u v) (star (Sum.elim u v)) := by
  ext (i | i) (j | j) <;> simp [Matrix.vecMulVec_apply]

/-- **L5 (Gram).** The coupled block `[[u u*, u v*], [v u*, v v*]]` is PSD. -/
theorem coupled_gram_posSemidef [Fintype n] [Fintype m] [PartialOrder R] [StarOrderedRing R]
    (u : n → R) (v : m → R) :
    (fromBlocks (vecMulVec u (star u)) (vecMulVec u (star v)) (vecMulVec v (star u))
        (vecMulVec v (star v))).PosSemidef := by
  rw [fromBlocks_vecMulVec]
  exact posSemidef_vecMulVec_self_star _

/-- **L5 (compressed coupled block).** If `[[A, B], [C, D]] ⪰ 0` then for any `Bu`, `Bv`,
`Buᴴ A Bu + Buᴴ B Bv + (Bvᴴ C Bu + Bvᴴ D Bv) ⪰ 0`. -/
theorem coupled_congr_posSemidef [Fintype n] [Fintype m] [PartialOrder R] {k : Type*}
    [Fintype k] {A : Matrix n n R} {B : Matrix n m R} {C : Matrix m n R} {D : Matrix m m R}
    (h : (fromBlocks A B C D).PosSemidef) (Bu : Matrix n k R) (Bv : Matrix m k R) :
    (Buᴴ * A * Bu + Buᴴ * B * Bv + (Bvᴴ * C * Bu + Bvᴴ * D * Bv)).PosSemidef := by
  have key : (fromRows Bu Bv)ᴴ * (fromBlocks A B C D * fromRows Bu Bv) =
      Buᴴ * A * Bu + Buᴴ * B * Bv + (Bvᴴ * C * Bu + Bvᴴ * D * Bv) := by
    rw [fromBlocks_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  have hc := h.conjTranspose_mul_mul_same (fromRows Bu Bv)
  rw [Matrix.mul_assoc, key] at hc
  exact hc

/-- **L5 (coupled block from rank-one moments).** -/
theorem coupled_rankOne_congr_posSemidef [Fintype n] [Fintype m] [PartialOrder R]
    [StarOrderedRing R] {k : Type*} [Fintype k] (u : n → R) (v : m → R) (Bu : Matrix n k R)
    (Bv : Matrix m k R) :
    (Buᴴ * vecMulVec u (star u) * Bu + Buᴴ * vecMulVec u (star v) * Bv +
      (Bvᴴ * vecMulVec v (star u) * Bu + Bvᴴ * vecMulVec v (star v) * Bv)).PosSemidef :=
  coupled_congr_posSemidef (coupled_gram_posSemidef u v) Bu Bv

end Gram

section Rearrangement

variable {κ ι R : Type*} [Fintype κ] [CommRing R] [StarRing R]

/-- A literal index rearrangement of an operator on `κ` copies of a space indexed by `ι`:
the `2|κ|` digit slots of the input (row digits `Sum.inl s`, column digits `Sum.inr s`) are
filled from the output slots through the bijection `σ`. -/
def rearr (σ : κ ⊕ κ ≃ κ ⊕ κ) (A : Matrix (κ → ι) (κ → ι) R) : Matrix (κ → ι) (κ → ι) R :=
  Matrix.of fun x y =>
    A (fun s => Sum.elim x y (σ (Sum.inl s))) (fun s => Sum.elim x y (σ (Sum.inr s)))

/-- The factor that ends up in output slot `p`: input row factor `a s` if `σ⁻¹ p = inl s`, the
conjugate input column factor `conj (b s)` if `σ⁻¹ p = inr s`. -/
def slotFn (σ : κ ⊕ κ ≃ κ ⊕ κ) (a b : κ → ι → R) (p : κ ⊕ κ) : ι → R :=
  Sum.elim a (fun s => star (b s)) (σ.symm p)

theorem rearr_add (σ : κ ⊕ κ ≃ κ ⊕ κ) (A B : Matrix (κ → ι) (κ → ι) R) :
    rearr σ (A + B) = rearr σ A + rearr σ B := by
  ext x y
  simp [rearr]

theorem rearr_smul (σ : κ ⊕ κ ≃ κ ⊕ κ) (c : R) (A : Matrix (κ → ι) (κ → ι) R) :
    rearr σ (c • A) = c • rearr σ A := by
  ext x y
  simp [rearr]

/-- **L5 (literal rearrangement of a rank-one product operator).**
`rearr σ |⊗a⟩⟨⊗b| = |⊗u⟩⟨⊗v|` with `u r = slotFn σ a b (inl r)` and
`v r = conj (slotFn σ a b (inr r))`. -/
theorem rearr_vecMulVec_prodVec (σ : κ ⊕ κ ≃ κ ⊕ κ) (a b : κ → ι → R) :
    rearr σ (vecMulVec (prodVec a) (star (prodVec b))) =
      vecMulVec (prodVec fun r => slotFn σ a b (Sum.inl r))
        (star (prodVec fun r => star (slotFn σ a b (Sum.inr r)))) := by
  ext x y
  have lhs : rearr σ (vecMulVec (prodVec a) (star (prodVec b))) x y =
      ∏ q, Sum.elim a (fun s => star (b s)) q (Sum.elim x y (σ q)) := by
    rw [Fintype.prod_sum_type]
    simp only [rearr, Matrix.of_apply, Matrix.vecMulVec_apply, prodVec, Pi.star_apply, star_prod, Sum.elim_inl,
      Sum.elim_inr]
  have rhs : vecMulVec (prodVec fun r => slotFn σ a b (Sum.inl r))
        (star (prodVec fun r => star (slotFn σ a b (Sum.inr r)))) x y =
      ∏ p, Sum.elim a (fun s => star (b s)) (σ.symm p) (Sum.elim x y p) := by
    rw [Fintype.prod_sum_type]
    simp only [slotFn, Matrix.vecMulVec_apply, prodVec, Pi.star_apply, star_prod, star_star, Sum.elim_inl,
      Sum.elim_inr]
  rw [lhs, rhs]
  have hperm := Equiv.prod_comp σ
    (fun p => Sum.elim a (fun s => star (b s)) (σ.symm p) (Sum.elim x y p))
  simpa only [Equiv.symm_apply_apply] using hperm

/-- **L5 (abstract coupled block).** If literal rearrangements of the three moment operators give
`|u⟩⟨u|`, `|u⟩⟨v|`, `|v⟩⟨u|`, `|v⟩⟨v|`, the assembled coupled block is PSD. -/
theorem coupled_block_of_rearr_posSemidef [Fintype ι] [DecidableEq κ] [PartialOrder R]
    [StarOrderedRing R] (σ₁ σ₂ σ₃ σ₄ : κ ⊕ κ ≃ κ ⊕ κ) (Y₁ Y₂ Y₃ Y₄ : Matrix (κ → ι) (κ → ι) R)
    (u v : (κ → ι) → R) (h₁ : rearr σ₁ Y₁ = vecMulVec u (star u))
    (h₂ : rearr σ₂ Y₂ = vecMulVec u (star v)) (h₃ : rearr σ₃ Y₃ = vecMulVec v (star u))
    (h₄ : rearr σ₄ Y₄ = vecMulVec v (star v)) :
    (fromBlocks (rearr σ₁ Y₁) (rearr σ₂ Y₂) (rearr σ₃ Y₃) (rearr σ₄ Y₄)).PosSemidef := by
  rw [h₁, h₂, h₃, h₄]
  exact coupled_gram_posSemidef u v

/-- **L5 (abstract coupled block, three rearrangements).** The form the verifier uses: the
(2,1) block is the conjugate transpose of the (1,2) block (the verifier's factor 2 on the
22-term). If `rearr σ₁ Y₁ = |u⟩⟨u|`, `rearr σ₂ Y₂ = |u⟩⟨v|` and `rearr σ₃ Y₃ = |v⟩⟨v|`, then
`[[rearr σ₁ Y₁, rearr σ₂ Y₂], [(rearr σ₂ Y₂)ᴴ, rearr σ₃ Y₃]] ⪰ 0`. -/
theorem coupled_block_of_rearr₃_posSemidef [Fintype ι] [DecidableEq κ] [PartialOrder R]
    [StarOrderedRing R] (σ₁ σ₂ σ₃ : κ ⊕ κ ≃ κ ⊕ κ) (Y₁ Y₂ Y₃ : Matrix (κ → ι) (κ → ι) R)
    (u v : (κ → ι) → R) (h₁ : rearr σ₁ Y₁ = vecMulVec u (star u))
    (h₂ : rearr σ₂ Y₂ = vecMulVec u (star v)) (h₃ : rearr σ₃ Y₃ = vecMulVec v (star v)) :
    (fromBlocks (rearr σ₁ Y₁) (rearr σ₂ Y₂) (rearr σ₂ Y₂)ᴴ (rearr σ₃ Y₃)).PosSemidef := by
  have hc : (vecMulVec u (star v))ᴴ = vecMulVec v (star u) := by
    rw [conjTranspose_vecMulVec, star_star]
  rw [h₁, h₂, h₃, hc]
  exact coupled_gram_posSemidef u v

end Rearrangement

end WernerEndpoint

#print axioms WernerEndpoint.fromBlocks_vecMulVec
#print axioms WernerEndpoint.coupled_gram_posSemidef
#print axioms WernerEndpoint.coupled_congr_posSemidef
#print axioms WernerEndpoint.coupled_rankOne_congr_posSemidef
#print axioms WernerEndpoint.rearr_add
#print axioms WernerEndpoint.rearr_smul
#print axioms WernerEndpoint.rearr_vecMulVec_prodVec
#print axioms WernerEndpoint.coupled_block_of_rearr_posSemidef
#print axioms WernerEndpoint.coupled_block_of_rearr₃_posSemidef
