import WernerEndpoint.AllD_Limit
import WernerEndpoint.Embedding
import WernerEndpoint.L9_Pairing

/-!
# The abstract all-d theorem: a `t = 0` certificate proves the three-copy endpoint in every `d`

A **block specification** (`BlockSpec`) is the data of one block of `verify_t0.py`:

* its kind — a word block of family `f` and cut `T`, or the coupled block `c3` (`T = {3}`) or
  `c23` (`T = {2,3}`);
* the walled-Brauer table `tab` of its cut;
* the three site modules, given by their `t`-polynomial matrices `N_i(p)(t)` of size `k_i`
  (`sites.json`, `N`);
* the qubit module `Fq(p) = Jᵀ Γ_T(P_p) J` (`qubit.json`: `E_q = G π = Jᵀ Γ_T(P_p) J`);
* the basis `B` (word) or the pair `Bu = B`, `Bv` (coupled), columns `Fin n`.

Its value at a trace-coordinate vector `μ` (`BlockSpec.L`) is `Bᵀ L₀(μ_f) B` for a word block and
`[Bu; Bv]ᵀ [[L₃₁, L₂₂], [L₂₂ᵀ, L₁₃]] [Bu; Bv]` for a coupled block, with
`L_f = blockOp N(0) Fq m_f (μ_f)` the full operator at `t = 0` (the verifier's `M_b(m)`, up to the
positive integer scalings `D_r` of `E_r = D_r N_r(0)`, which `blockOp_smul_sites` removes).

`BlockSpec.Valid`: the cut is one of the verifier's, the table holds at every `d ≥ 4`
(`TabAt`), every site module is a `SiteCert` ((A2)–(A4)), and the qubit module is
`QubitAt` ((B)).

**`BlockSpec.L_posSemidef`** (steps 1–6 for one block): a valid block is PSD at every
trace-coordinate vector of every local dimension.

**`endpoint_of_t0_cert`** (step 7, pairing): if valid blocks, PSD multipliers `X_b`, rows that
are physically valid with values `v_r`, and multipliers `λ_r` with `∑ λ_r v_r ≥ 0` satisfy the
identity `obj(μ) = ∑_b ⟨X_b, L_b(μ)⟩ + ∑_r λ_r row_r(μ)` for every orbit-invariant `μ`, then
`q(C) ≥ 0` for every rank-`≤ 2` operator `C` on `(ℂ^e)^{⊗3}`, for **every** `e`.
-/

open Matrix Polynomial
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

/-- The kind of a block. -/
inductive BKind
  | word (f : Fam) (T : Finset (Fin 4))
  | c3
  | c23

/-- The cut of a block. -/
def BKind.cut : BKind → Finset (Fin 4)
  | .word _ T => T
  | .c3 => {3}
  | .c23 => {2, 3}

/-- One block of the `t = 0` certificate. -/
structure BlockSpec (κ : Type) [Fintype κ] [DecidableEq κ] where
  kind : BKind
  tab : P4 → P4 → P4 × ℕ
  k : κ → ℕ
  N : (i : κ) → P4 → Matrix (Fin (k i)) (Fin (k i)) ℝ[X]
  kq : ℕ
  Fq : P4 → Matrix (Fin kq) (Fin kq) ℝ
  J : Matrix (Fin 4 → Fin 2) (Fin kq) ℝ
  n : ℕ
  B : Matrix (((i : κ) → Fin (k i)) × Fin kq) (Fin n) ℝ
  Bv : Matrix (((i : κ) → Fin (k i)) × Fin kq) (Fin n) ℝ

variable {κ : Type} [Fintype κ] [DecidableEq κ]

namespace BlockSpec

/-- The `t = 0` site matrices `N_i(p)(0)`. -/
abbrev N0 (b : BlockSpec κ) : (i : κ) → P4 → Matrix (Fin (b.k i)) (Fin (b.k i)) ℝ :=
  fun i p => evalM 0 (b.N i p)

/-- The full coupled operator `[[L₃₁, L₂₂], [L₂₂ᵀ, L₁₃]]` at `t = 0`. -/
def coupledOp (b : BlockSpec κ) (mp₁ mp₂ mp₃ : P4 ≃ P4) (μ : Fam → Tup κ → ℝ) :=
  fromBlocks (blockOp b.N0 b.Fq mp₁ (μ .f31)) (blockOp b.N0 b.Fq mp₂ (μ .f22))
    (blockOp b.N0 b.Fq mp₂ (μ .f22))ᵀ (blockOp b.N0 b.Fq mp₃ (μ .f13))

/-- **The block value at `t = 0`** (the verifier's `M_b(m)`). -/
def L (b : BlockSpec κ) (μ : Fam → Tup κ → ℝ) : Matrix (Fin b.n) (Fin b.n) ℝ :=
  match b.kind with
  | .word f _ => b.Bᵀ * blockOp b.N0 b.Fq (Equiv.refl P4) (μ f) * b.B
  | .c3 => (fromRows b.B b.Bv)ᵀ *
      b.coupledOp (mpE mT3_31 mT3_31_surj) (mpE mT3_22 mT3_22_surj) (mpE mT3_13 mT3_13_surj) μ *
      fromRows b.B b.Bv
  | .c23 => (fromRows b.B b.Bv)ᵀ *
      b.coupledOp (mpE mT23_31 mT23_31_surj) (mpE mT23_22 mT23_22_surj)
        (mpE mT23_13 mT23_13_surj) μ * fromRows b.B b.Bv

/-- **Validity of a block** (what layer D proves from `verify_t0.py`'s checks (A0)–(A4), (B)). -/
def Valid (b : BlockSpec κ) : Prop :=
  IsCut b.kind.cut ∧ (∀ d : ℕ, 4 ≤ d → TabAt b.kind.cut d b.tab) ∧
    (∀ i, SiteCert b.tab (b.N i)) ∧ QubitAt b.kind.cut b.Fq b.J

/-- **Steps 1–6 for one block.** A valid block is PSD at every trace-coordinate vector of every
local dimension `e`. -/
theorem L_posSemidef {b : BlockSpec κ} (hb : b.Valid) {e : ℕ} {a a' : (κ → Fin e) × Fin 2 → ℂ}
    {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a a' μ) : (b.L μ).PosSemidef := by
  obtain ⟨hT, htab, hN, hJ⟩ := hb
  unfold L
  cases hk : b.kind with
  | word f T =>
    simp only [hk, BKind.cut] at hT htab hJ
    have := (blockOp_word_t0_posSemidef hT htab b.N hN hJ hμ f).conjTranspose_mul_mul_same b.B
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  | c3 =>
    simp only [hk, BKind.cut] at htab hJ
    have := (blockOp_coupled_T3_t0_posSemidef htab b.N hN hJ hμ).conjTranspose_mul_mul_same
      (fromRows b.B b.Bv)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  | c23 =>
    simp only [hk, BKind.cut] at htab hJ
    have := (blockOp_coupled_T23_t0_posSemidef htab b.N hN hJ hμ).conjTranspose_mul_mul_same
      (fromRows b.B b.Bv)
    rwa [conjTranspose_eq_transpose_of_trivial] at this

end BlockSpec

/-- Positive scalings of the site matrices (the verifier's `E_r = D_r N_r(0)`, `D_r > 0`) scale
the full operator by `∏ D_i`. -/
theorem blockOp_smul_sites {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (D : κ → ℝ) (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (Fq : P4 → Matrix Kq Kq ℝ)
    (mp : P4 ≃ P4) (m : Tup κ → ℝ) :
    blockOp (fun i p => D i • N i p) Fq mp m = (∏ i, D i) • blockOp N Fq mp m := by
  unfold blockOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_comm]
  congr 1
  ext X Y
  simp only [rtens, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  ring

/-- **The abstract all-d theorem (step 7).** A `t = 0` certificate of the shape checked by
`verify_t0.py` proves `q(C) ≥ 0` for every rank-`≤ 2` `C` on `(ℂ^e)^{⊗3}`, for every `e`. -/
theorem endpoint_of_t0_cert {β : Type} [Fintype β] (blk : β → BlockSpec (Fin 3))
    (hblk : ∀ j, (blk j).Valid)
    (X : (j : β) → Matrix (Fin (blk j).n) (Fin (blk j).n) ℝ) (hX : ∀ j, (X j).PosSemidef)
    {γ : Type} [Fintype γ] (rows : γ → Row (Fin 3)) (lam val : γ → ℝ)
    (hrow : ∀ r, RowValid (Fin 3) (rows r) (val r)) (hval : 0 ≤ ∑ r, lam r * val r)
    (hid : ∀ μ : Fam → Tup (Fin 3) → ℝ, OrbInv (Fin 3) μ →
      mObj 2 μ = ∑ j, ∑ i, ∑ i', X j i i' * (blk j).L μ i i' +
        ∑ r, lam r * mRowVal 2 (rows r) μ)
    (e : ℕ) (C : Matrix (Fin 3 → Fin e) (Fin 3 → Fin e) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  refine qfun_nonneg_of_larger (le_max_left e 2) (fun C hC => ?_) C hC
  have hH : 2 ≤ Fintype.card (Fin 3 → Fin (max e 2)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc 2 ≤ max e 2 := le_max_right e 2
      _ = max e 2 ^ 1 := (pow_one _).symm
      _ ≤ max e 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  refine qfun_nonneg_of_twirl hH (fun a b hab => ?_) C hC
  obtain ⟨μ, hμ, horb⟩ := exists_mcoord (κ := Fin 3) a b
  have hobj := mObj_eq_trace hμ
  simp only [Fintype.card_fin] at hobj
  rw [← hobj, hid μ horb]
  have hrows : ∀ r, mRowVal 2 (rows r) μ = val r := by
    intro r
    have := mRowVal_eq hμ (rows r)
    simp only [Fintype.card_fin] at this
    rw [this]
    exact hrow r _ a b hab
  simp only [hrows]
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) hval
  exact pairing_nonneg_real (hX j) (BlockSpec.L_posSemidef (hblk j) hμ)

/-- **The three-copy Werner endpoint for every `d`, from a `t = 0` certificate**, stated with
`(Fin d)^{⊗3}` sites. (Same as `endpoint_of_t0_cert`; the name records the target.) -/
theorem werner3_endpoint_all_d_of_t0_cert {β : Type} [Fintype β] (blk : β → BlockSpec (Fin 3))
    (hblk : ∀ j, (blk j).Valid)
    (X : (j : β) → Matrix (Fin (blk j).n) (Fin (blk j).n) ℝ) (hX : ∀ j, (X j).PosSemidef)
    {γ : Type} [Fintype γ] (rows : γ → Row (Fin 3)) (lam val : γ → ℝ)
    (hrow : ∀ r, RowValid (Fin 3) (rows r) (val r)) (hval : 0 ≤ ∑ r, lam r * val r)
    (hid : ∀ μ : Fam → Tup (Fin 3) → ℝ, OrbInv (Fin 3) μ →
      mObj 2 μ = ∑ j, ∑ i, ∑ i', X j i i' * (blk j).L μ i i' +
        ∑ r, lam r * mRowVal 2 (rows r) μ) :
    ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ qfun C :=
  endpoint_of_t0_cert blk hblk X hX rows lam val hrow hval hid

end WernerEndpoint

end

#print axioms WernerEndpoint.BlockSpec.L_posSemidef
#print axioms WernerEndpoint.blockOp_smul_sites
#print axioms WernerEndpoint.endpoint_of_t0_cert
#print axioms WernerEndpoint.werner3_endpoint_all_d_of_t0_cert
