import WernerEndpoint.AllD_MCoord
import WernerEndpoint.AllD_CP

/-!
# All-d lemma chain, step 5: the t-blocks at `t = 1/d` are PSD at physical points

Notation. `κ` sites, local space `Fin d`, qubit `Fin 2`. A *site module* of a cut `T` is a family
of real matrices `F(p)` (`p ∈ S₄`, the verifier's `F_r(p)(d)` at a fixed `d`), a *t-module* is
`N(p)` (the verifier's `N_r(p)(t)` evaluated at `t = 1/d`), and a *qubit module* is
`Fq(p) = Jᵀ Γ_T(P_p) J` for a real embedding `J` of `(ℂ²)^{⊗4}` (verifier (B)).

* `blockOp N Fq mp m = ∑_s m(s) (⊗_i N_i(mp s_i)) ⊗ Fq(mp s_q)` is the **full, uncompressed**
  operator of a block in trace coordinates (`mp = id` for word blocks, the coupled diagram map for
  the coupled blocks); `wordBlock` and `coupledBlock` are its compressions by an arbitrary real
  basis `B`, or by a stacked basis `[Bu; Bv]`.
* `TabAt T d tab`: the walled-Brauer table of the cut, `Γ_T(P_p) Γ_T(P_q) = d^{l} Γ_T(P_s)`.
* `ModuleAt d tab F`: `d^{l(p⁻¹,q)} F(s(p⁻¹,q)) = F(p)ᵀ H F(q)` for a PSD `H` (from (A2)–(A3):
  `moduleAt_of_verifier`, with `H = F(e)⁻¹`).
* `QubitAt T Fq J`: `Fq(p) = Jᵀ Γ_T(P_p) J`.
* Weingarten relation (verifier (A4)): `∑_{p'} G_d(p, p') N(p') = c F(p)` with `c > 0`.

**`blockOp_word_posSemidef`** (word blocks) and **`blockOp_coupled_posSemidef_of`** (the 2×2 coupled
operator): at every `d ≥ 4`, for every trace-coordinate vector `μ` of a lift at local dimension
`d`, the full operator built from `N(1/d)` is PSD. Hence so is every compression
(`wordBlock_posSemidef`, `fromRows_compress` with `conjTranspose_mul_mul_same`), for any real `B`, `Bu`, `Bv` (item 5).
The proof: `Ŷ = ∑ y_t P_t` with `y = (Wg ⊗ I) μ` (`rep_of_mcoord`); `Γ_T(Ŷ)` (resp. the 2×2
rearranged block of layer C) is PSD; complete positivity of the site modules
(`cp_of_module`, item 3) and the qubit compression give `∑_t y_t (⊗F(t_i)) ⊗ Fq(t_q) ⪰ 0`; the
Weingarten relation turns this into `(∏ c_i)⁻¹ ∑_s μ_s (⊗N(s_i)) ⊗ Fq(s_q)`, and the coupled
maps preserve `G_d` (item 4).
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section RealComplex

variable {m n : Type*} [Fintype n]

/-- Real matrices as complex matrices. -/
abbrev cmap {m' : Type*} (M : Matrix m m' ℝ) : Matrix m m' ℂ := M.map (fun r => (r : ℂ))

theorem cmap_mul {l : Type*} (A : Matrix m n ℝ) (B : Matrix n l ℝ) :
    cmap (A * B) = cmap A * cmap B := by
  ext i j; simp [Matrix.mul_apply]

theorem cmap_conjTranspose {m' : Type*} (A : Matrix m m' ℝ) : (cmap A)ᴴ = cmap Aᵀ := by
  ext i j; simp

theorem cmap_smul {m' : Type*} (c : ℝ) (A : Matrix m m' ℝ) : cmap (c • A) = (c : ℂ) • cmap A := by
  ext i j; simp

theorem cmap_sum {m' β : Type*} (s : Finset β) (A : β → Matrix m m' ℝ) :
    cmap (∑ b ∈ s, A b) = ∑ b ∈ s, cmap (A b) := by
  ext i j; simp [Matrix.sum_apply]

theorem cmap_injective {m' : Type*} : Function.Injective (cmap (m := m) (m' := m')) := by
  intro A B h; ext i j
  have := congrFun (congrFun h i) j
  simpa using this

/-- Real vectors as complex vectors. -/
abbrev cvec (u : n → ℝ) : n → ℂ := fun i => (u i : ℂ)

theorem cmap_mulVec (M : Matrix n n ℝ) (u : n → ℝ) : cmap M *ᵥ cvec u = cvec (M *ᵥ u) := by
  funext i; simp [mulVec, dotProduct, cvec, Complex.ofReal_sum]

theorem cvec_dotProduct (u w : n → ℝ) : cvec u ⬝ᵥ cvec w = ((u ⬝ᵥ w : ℝ) : ℂ) := by
  simp [dotProduct]

theorem star_cvec (u : n → ℝ) : star (cvec u) = cvec u := by
  funext i; simp

theorem cmap_isHermitian {M : Matrix n n ℝ} (h : M.IsHermitian) : (cmap M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [cmap_conjTranspose, ← conjTranspose_eq_transpose_of_trivial, h.eq]

/-- A real matrix that is PSD as a complex matrix is PSD. -/
theorem posSemidef_of_cmap {M : Matrix n n ℝ} (h : (cmap M).PosSemidef) : M.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : cmap Mᵀ = cmap M := by rw [← cmap_conjTranspose]; exact h.1
    have := cmap_injective h1
    unfold Matrix.IsHermitian
    rwa [conjTranspose_eq_transpose_of_trivial]
  · have := h.2 (cvec x)
    rw [star_cvec, cmap_mulVec, cvec_dotProduct] at this
    simpa using Complex.zero_le_real.mp this

/-- A real PSD matrix is PSD as a complex matrix. -/
theorem cmap_posSemidef {M : Matrix n n ℝ} (h : M.PosSemidef) : (cmap M).PosSemidef := by
  have hsym : ∀ u w : n → ℝ, u ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ u) := by
    intro u w
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
      ← conjTranspose_eq_transpose_of_trivial, h.1.eq]
  refine ⟨cmap_isHermitian h.1, fun x => ?_⟩
  let u : n → ℝ := fun i => (x i).re
  let v : n → ℝ := fun i => (x i).im
  have hx : x = cvec u + Complex.I • cvec v := by
    funext i
    simp only [cvec, u, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hsx : star x = cvec u - Complex.I • cvec v := by
    funext i
    apply Complex.ext <;> simp [u, v]
  have key : star x ⬝ᵥ (cmap M *ᵥ x) =
      (cvec u - Complex.I • cvec v) ⬝ᵥ (cmap M *ᵥ (cvec u + Complex.I • cvec v)) := by
    rw [← hsx, ← hx]
  rw [key]
  simp only [mulVec_add, mulVec_smul, cmap_mulVec, sub_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, cvec_dotProduct, smul_eq_mul]
  rw [hsym v u]
  have hu := h.2 u
  have hv := h.2 v
  simp only [star_trivial] at hu hv
  convert Complex.zero_le_real.mpr (add_nonneg hu hv) using 1
  push_cast
  linear_combination (-((v ⬝ᵥ (M *ᵥ v) : ℝ) : ℂ)) * Complex.I_sq

end RealComplex

section Setup

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The one-site operators `Γ_T(P_p)`. -/
abbrev Osite (T : Finset (Fin 4)) (α : Type*) [Fintype α] [DecidableEq α] (p : P4) :
    Matrix (Fin 4 → α) (Fin 4 → α) ℂ :=
  ptrans (ι := fun _ : Fin 4 => α) T (sP α p)

theorem sP_conjTranspose (α : Type*) [Fintype α] [DecidableEq α] (p : P4) :
    (sP α p)ᴴ = sP α p⁻¹ := by
  ext x y
  simp only [sP, conjTranspose_apply, Matrix.of_apply]
  by_cases h : x = y ∘ p
  · rw [if_pos h, if_pos]; · simp
    rw [h]; funext k; simp
  · rw [if_neg h, if_neg]; · simp
    intro h'; apply h; rw [h']; funext k; simp

theorem sP_one (α : Type*) [Fintype α] [DecidableEq α] : sP α (1 : P4) = 1 := by
  ext x y
  simp only [sP, Matrix.of_apply, Matrix.one_apply, Equiv.Perm.coe_one, Function.comp_id]
  by_cases h : x = y
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The walled-Brauer table of the cut `T` at local dimension `d`. -/
def TabAt (T : Finset (Fin 4)) (d : ℕ) (tab : P4 → P4 → P4 × ℕ) : Prop :=
  ∀ p q, Osite T (Fin d) p * Osite T (Fin d) q = ((d ^ (tab p q).2 : ℕ) : ℂ) • Osite T (Fin d) (tab p q).1

/-- A site module at local dimension `d`: `d^{l(p⁻¹,q)} F(s(p⁻¹,q)) = F(p)ᵀ H F(q)`, `H ⪰ 0`. -/
def ModuleAt {k : Type*} [Fintype k] (d : ℕ) (tab : P4 → P4 → P4 × ℕ) (F : P4 → Matrix k k ℝ) :
    Prop :=
  ∃ H : Matrix k k ℝ, H.PosSemidef ∧
    ∀ p q, ((d : ℝ) ^ (tab p⁻¹ q).2) • F (tab p⁻¹ q).1 = (F p)ᵀ * H * F q

/-- **From the verifier's (A2)–(A3)**: `F(p)ᵀ = F(p⁻¹)`,
`F(p) adj F(e) F(q) = d^{l(p,q)} det F(e) F(s(p,q))` and `F(e) ≻ 0` give a module. -/
theorem moduleAt_of_verifier {k : Type*} [Fintype k] [DecidableEq k] {d : ℕ}
    {tab : P4 → P4 → P4 × ℕ} {F : P4 → Matrix k k ℝ} (hT : ∀ p, (F p)ᵀ = F p⁻¹)
    (hhom : ∀ p q, F p * (F 1).adjugate * F q = ((d : ℝ) ^ (tab p q).2 * (F 1).det) • F (tab p q).1)
    (hpd : (F 1).PosDef) : ModuleAt d tab F := by
  refine ⟨(F 1)⁻¹, hpd.inv.posSemidef, fun p q => ?_⟩
  have hdet : (F 1).det ≠ 0 := ne_of_gt hpd.det_pos
  rw [hT p, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_mul, hhom, smul_smul]
  rw [show (Ring.inverse (F 1).det * ((d : ℝ) ^ (tab p⁻¹ q).2 * (F 1).det)) =
    (d : ℝ) ^ (tab p⁻¹ q).2 by rw [Ring.inverse_eq_inv']; field_simp]

/-- A qubit module: `Fq(p) = Jᵀ Γ_T(P_p) J` with a real `J`. -/
def QubitAt {Kq : Type*} [Fintype Kq] (T : Finset (Fin 4)) (Fq : P4 → Matrix Kq Kq ℝ)
    (J : Matrix (Fin 4 → Fin 2) Kq ℝ) : Prop :=
  ∀ p, cmap (Fq p) = (cmap J)ᴴ * Osite T (Fin 2) p * cmap J

/-! ### Splitting the four-replica index into sites and qubit -/

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-- `X ↦ ((siteDig X i)_i, qDig X)`. -/
def splitX : (Fin 4 → (κ → ι) × ρ) ≃ (κ → Fin 4 → ι) × (Fin 4 → ρ) where
  toFun X := (fun i k => (X k).1 i, fun k => (X k).2)
  invFun Z := fun k => (fun i => Z.1 i k, Z.2 k)
  left_inv X := rfl
  right_inv Z := rfl

theorem sprod_eq_submatrix (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ)
    (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    sprod A B = (gtens (K := fun _ : κ => Fin 4 → ι) (K' := fun _ : κ => Fin 4 → ι) A B).submatrix
      splitX splitX := by
  ext X Y; rfl

/-- Componentwise image of a diagram tuple. -/
def mpT (mp : P4 ≃ P4) (t : Tup κ) : Tup κ := (fun i => mp (t.1 i), mp t.2)

/-- The coefficient of `⊗_i Γ_T(P_{u_i})` in `∑_t y_t Γ_T(P_{mp t})`. -/
def Rphys (T : Finset (Fin 4)) (ρ : Type*) [Fintype ρ] [DecidableEq ρ] (mp : P4 ≃ P4)
    (y : Tup κ → ℝ) (u : κ → P4) : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ :=
  ∑ q, ((y (fun i => mp.symm (u i), q) : ℝ) : ℂ) • Osite T ρ (mp q)

theorem submatrix_sum' {a b β : Type*} (s : Finset β) (A : β → Matrix a a ℂ) (e : b → a) :
    (∑ x ∈ s, A x).submatrix e e = ∑ x ∈ s, (A x).submatrix e e := by
  ext i j; simp [Matrix.sum_apply]

theorem sum_piCongr {M : Type*} [AddCommMonoid M] (mp : P4 ≃ P4) (G : (κ → P4) → M) :
    ∑ ts : κ → P4, G (fun i => mp (ts i)) = ∑ u, G u :=
  Equiv.sum_comp (Equiv.piCongrRight fun _ : κ => mp) G

theorem phys_eq (T : Finset (Fin 4)) (mp : P4 ≃ P4) (y : Tup κ → ℝ) :
    ∑ t, ((y t : ℝ) : ℂ) • PT ι ρ T (mpT mp t) =
      (∑ u, tensO (Osite T ι) u (Rphys T ρ mp y u)).submatrix splitX splitX := by
  have h1 : ∑ t, ((y t : ℝ) : ℂ) • PT ι ρ T (mpT mp t) =
      (∑ t, ((y t : ℝ) : ℂ) • tensO (Osite T ι) (fun i => mp (t.1 i))
        (Osite T ρ (mp t.2))).submatrix splitX splitX := by
    rw [submatrix_sum']
    simp only [submatrix_smul, PT_eq_sprod, sprod_eq_submatrix, mpT]
    rfl
  rw [h1]
  congr 1
  rw [Fintype.sum_prod_type, ← sum_piCongr mp (fun u => tensO (Osite T ι) u (Rphys T ρ mp y u))]
  refine Finset.sum_congr rfl fun ts _ => ?_
  simp only [Rphys, Equiv.symm_apply_apply, gtens_sum, gtens_smul]

/-- The qubit compression `(1 ⊗ J)ᴴ (·) (1 ⊗ J)`. -/
theorem compress_sum {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    {W Kq : Type*} [Fintype W] [DecidableEq W] [Fintype Kq] [DecidableEq Kq]
    (A : (κ → P4) → (i : κ) → Matrix (K i) (K i) ℂ) (R : (κ → P4) → Matrix W W ℂ)
    (Jc : Matrix W Kq ℂ) :
    (gtens (K := K) (K' := K) (fun _ => 1) Jc)ᴴ * (∑ u, gtens (A u) (R u)) * gtens (fun _ => 1) Jc =
      ∑ u, gtens (A u) (Jcᴴ * R u * Jc) := by
  rw [gtens_conjTranspose, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [gtens_mul, gtens_mul]
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- `gtens` is multilinear in the site factors. -/
theorem gtens_sum_left {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    {W : Type*} [Fintype W] [DecidableEq W] {Jx : Type*} [Fintype Jx]
    (a : κ → Jx → ℂ) (B : (i : κ) → Jx → Matrix (K i) (K i) ℂ) (S : Matrix W W ℂ) :
    gtens (fun i => ∑ j, a i j • B i j) S =
      ∑ s : κ → Jx, (∏ i, a i (s i)) • gtens (fun i => B i (s i)) S := by
  ext X Y
  simp only [gtens, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib]; ring

theorem mod_eq {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)] {T : Finset (Fin 4)}
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J) (A : (i : κ) → P4 → Matrix (K i) (K i) ℂ)
    (mp : P4 ≃ P4) (y : Tup κ → ℝ) :
    ∑ u, gtens (fun i => A i (u i)) ((cmap J)ᴴ * Rphys T (Fin 2) mp y u * cmap J) =
      ∑ t, ((y t : ℝ) : ℂ) • gtens (fun i => A i (mp (t.1 i))) (cmap (Fq (mp t.2))) := by
  have hJ' : ∀ p, (cmap J)ᴴ * Osite T (Fin 2) p * cmap J = cmap (Fq p) := fun p => (hJ p).symm
  rw [← sum_piCongr mp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ts _ => ?_
  simp only [Rphys, Equiv.symm_apply_apply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, hJ', gtens_sum, gtens_smul]

/-- **Weingarten step.** With `∑_{p'} G_d(p,p') N(p') = c F(p)` and a `G_d`-preserving bijection
`mp`, the module operator in diagram coefficients `y` equals `(∏ c_i)⁻¹` times the operator built
from `N` in trace coordinates `μ = (G_d ⊗ I) y`. -/
theorem weingarten_eq {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    {W : Type*} [Fintype W] [DecidableEq W] {d : ℕ}
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℂ) (c : κ → ℂ) (hc : ∀ i, c i ≠ 0)
    (hW : ∀ i p, ∑ p', (gram d p p' : ℂ) • N i p' = c i • F i p)
    (mp : P4 ≃ P4) (hg : ∀ a b, gram d (mp a) (mp b) = gram d a b)
    (S : P4 → Matrix W W ℂ) (y : Tup κ → ℝ) :
    ∑ t, ((y t : ℝ) : ℂ) • gtens (fun i => F i (mp (t.1 i))) (S t.2) =
      (∏ i, (c i)⁻¹) • ∑ s, ((siteG d y s : ℝ) : ℂ) • gtens (fun i => N i (mp (s.1 i))) (S s.2) := by
  have hF : ∀ i p, F i (mp p) = (c i)⁻¹ • ∑ s, (gram d p s : ℂ) • N i (mp s) := by
    intro i p
    have h1 : F i (mp p) = (c i)⁻¹ • (c i • F i (mp p)) := by
      rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [h1, ← hW, ← Equiv.sum_comp mp]
    simp only [hg]
  have hterm : ∀ (ts : κ → P4) (q : P4), gtens (fun i => F i (mp (ts i))) (S q) =
      (∏ i, (c i)⁻¹) • ∑ s : κ → P4, (∏ i, (gram d (ts i) (s i) : ℂ)) •
        gtens (fun i => N i (mp (s i))) (S q) := by
    intro ts q
    rw [show (fun i => F i (mp (ts i))) =
        fun i => (c i)⁻¹ • ∑ s, (gram d (ts i) s : ℂ) • N i (mp s) from funext fun i => hF i _]
    rw [gtens_smul_left, gtens_sum_left]
  let G : (κ → P4) → P4 → Matrix (((i : κ) → K i) × W) (((i : κ) → K i) × W) ℂ :=
    fun s q => gtens (fun i => N i (mp (s i))) (S q)
  calc ∑ t, ((y t : ℝ) : ℂ) • gtens (fun i => F i (mp (t.1 i))) (S t.2)
      = ∑ ts : κ → P4, ∑ q : P4, ∑ s : κ → P4,
          (((y (ts, q) : ℝ) : ℂ) * ((∏ i, (c i)⁻¹) * ∏ i, (gram d (ts i) (s i) : ℂ))) • G s q := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ts _ => Finset.sum_congr rfl fun q _ => ?_
        rw [hterm ts q, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [smul_smul, G]
    _ = ∑ ts : κ → P4, ∑ s : κ → P4, ∑ q : P4,
          (((y (ts, q) : ℝ) : ℂ) * ((∏ i, (c i)⁻¹) * ∏ i, (gram d (ts i) (s i) : ℂ))) • G s q := by
        refine Finset.sum_congr rfl fun ts _ => ?_
        exact Finset.sum_comm
    _ = ∑ s : κ → P4, ∑ ts : κ → P4, ∑ q : P4,
          (((y (ts, q) : ℝ) : ℂ) * ((∏ i, (c i)⁻¹) * ∏ i, (gram d (ts i) (s i) : ℂ))) • G s q :=
        Finset.sum_comm
    _ = ∑ s : κ → P4, ∑ q : P4, ∑ ts : κ → P4,
          ((∏ i, (c i)⁻¹) * ((∏ i, (gram d (s i) (ts i) : ℂ)) * ((y (ts, q) : ℝ) : ℂ))) • G s q := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun ts _ => ?_
        congr 1
        have : ∏ i, (gram d (ts i) (s i) : ℂ) = ∏ i, (gram d (s i) (ts i) : ℂ) :=
          Finset.prod_congr rfl fun i _ => by rw [gram_symm]
        rw [this]
        ring
    _ = (∏ i, (c i)⁻¹) • ∑ s, ((siteG d y s : ℝ) : ℂ) •
          gtens (fun i => N i (mp (s.1 i))) (S s.2) := by
        rw [Finset.smul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
        simp only [siteG, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
          Finset.sum_smul, Finset.smul_sum, smul_smul, G]

/-! ### The block operators -/

/-- Real `(⊗_i A_i) ⊗ S`. -/
def rtens {K : κ → Type*} {Kq : Type*} (A : (i : κ) → Matrix (K i) (K i) ℝ) (S : Matrix Kq Kq ℝ) :
    Matrix (((i : κ) → K i) × Kq) (((i : κ) → K i) × Kq) ℝ :=
  Matrix.of fun X Y => (∏ i, A i (X.1 i) (Y.1 i)) * S X.2 Y.2

theorem cmap_rtens {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*}
    (A : (i : κ) → Matrix (K i) (K i) ℝ) (S : Matrix Kq Kq ℝ) :
    cmap (rtens A S) = gtens (fun i => cmap (A i)) (cmap S) := by
  ext X Y; simp [rtens, gtens]

/-- **The full (uncompressed) block operator in trace coordinates**:
`∑_s m(s) (⊗_i N_i(mp s_i)) ⊗ Fq(mp s_q)`. -/
def blockOp {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (Fq : P4 → Matrix Kq Kq ℝ) (mp : P4 ≃ P4)
    (m : Tup κ → ℝ) : Matrix (((i : κ) → K i) × Kq) (((i : κ) → K i) × Kq) ℝ :=
  ∑ s, m s • rtens (fun i => N i (mp (s.1 i))) (Fq (mp s.2))

theorem cmap_blockOp {K : κ → Type*} [∀ i, Fintype (K i)] {Kq : Type*} [Fintype Kq]
    (N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (Fq : P4 → Matrix Kq Kq ℝ) (mp : P4 ≃ P4)
    (m : Tup κ → ℝ) :
    cmap (blockOp N Fq mp m) =
      ∑ s, ((m s : ℝ) : ℂ) • gtens (fun i => cmap (N i (mp (s.1 i)))) (cmap (Fq (mp s.2))) := by
  simp only [blockOp, cmap_sum, cmap_smul, cmap_rtens]

/-! ### Complete positivity of the site modules at `d ≥ 4` -/

theorem diagFamily_site {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)} {tab : P4 → P4 → P4 × ℕ}
    (htab : TabAt T d tab) :
    DiagFamily (Osite T (Fin d)) (fun p q => (tab p q).1) (fun p q => ((d ^ (tab p q).2 : ℕ) : ℂ))
      (fun p => p⁻¹) 1 where
  mul := htab
  star p := by rw [Osite, ptrans_conjTranspose, sP_conjTranspose]
  one := by rw [Osite, sP_one, ptrans_one']
  dual p := dualEntry_ptrans_sP (Fin d) (by simpa using hd) T p

theorem cp_sites {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)} {tab : P4 → P4 → P4 × ℕ}
    (htab : TabAt T d tab) {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    {W : Type*} [Fintype W] [DecidableEq W] (R : (κ → P4) → Matrix W W ℂ)
    (hR : (∑ u, tensO (Osite T (Fin d)) u (R u)).PosSemidef) :
    (∑ u, gtens (fun i => cmap (F i (u i))) (R u)).PosSemidef := by
  choose H hH hmod using hF
  refine cp_of_module (diagFamily_site hd htab) (fun i p => cmap (F i p)) (fun i => cmap (H i))
    (fun i => cmap_posSemidef (hH i)) (fun i p q => ?_) R hR
  have := congrArg cmap (hmod i p q)
  rw [cmap_smul, cmap_mul, cmap_mul, ← cmap_conjTranspose] at this
  rw [← this]
  push_cast
  rfl

/-! ### Word blocks -/

theorem ptrans_sum_smul (T : Finset (Fin 4)) (y : Tup κ → ℝ) :
    ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (∑ t, ((y t : ℝ) : ℂ) • permOp ι ρ t.1 t.2) =
      ∑ t, ((y t : ℝ) : ℂ) • PT ι ρ T t := by
  show ptransL κ ι ρ T _ = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem mpT_refl (t : Tup κ) : mpT (Equiv.refl P4) t = t := rfl

/-- One block of the module operator: compression, Weingarten step, back to `blockOp`. -/
theorem module_block_eq {d : ℕ} {T : Finset (Fin 4)}
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ)
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J)
    (mp : P4 ≃ P4) (hg : ∀ a b, gram d (mp a) (mp b) = gram d a b) (y μf : Tup κ → ℝ)
    (hsite : siteG d y = μf) :
    ∑ u, gtens (fun i => cmap (F i (u i))) ((cmap J)ᴴ * Rphys T (Fin 2) mp y u * cmap J) =
      cmap ((∏ i, (c i)⁻¹) • blockOp N Fq mp μf) := by
  have hW' : ∀ i p, ∑ p', (gram d p p' : ℂ) • cmap (N i p') = (c i : ℂ) • cmap (F i p) := by
    intro i p
    have := congrArg cmap (hW i p)
    simpa [cmap_sum, cmap_smul] using this
  rw [mod_eq hJ (fun i p => cmap (F i p)) mp y,
    weingarten_eq (fun i p => cmap (F i p)) (fun i p => cmap (N i p)) (fun i => (c i : ℂ))
      (fun i => show (c i : ℂ) ≠ 0 from by exact_mod_cast (hc i).ne') hW' mp hg (fun q => cmap (Fq (mp q))) y,
    hsite, cmap_smul, cmap_blockOp]
  push_cast
  rfl

/-- **Step 5, word blocks (full operator).** -/
theorem blockOp_word_posSemidef {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)} (hT : IsCut T)
    {tab : P4 → P4 → P4 × ℕ} (htab : TabAt T d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J)
    {a b : (κ → Fin d) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) (f : Fam) :
    (blockOp N Fq (Equiv.refl P4) (μ f)).PosSemidef := by
  have hd0 : 0 < d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨hrep, hsite⟩ := rep_of_mcoord hd hμ f
  set y := siteWg d (μ f)
  -- the physical operator
  have hphys := twirl_ptrans_posSemidef (ι := Fin d) (ρ := Fin 2) hT f a b
  rw [hrep, ptrans_sum_smul] at hphys
  have e1 : ∑ t, ((y t : ℝ) : ℂ) • PT (Fin d) (Fin 2) T t =
      ∑ t, ((y t : ℝ) : ℂ) • PT (Fin d) (Fin 2) T (mpT (Equiv.refl P4) t) := rfl
  rw [e1, phys_eq, posSemidef_submatrix_equiv] at hphys
  have h1 := cp_sites hd htab F hF _ hphys
  have h2 := h1.conjTranspose_mul_mul_same (gtens (K := K) (K' := K) (fun _ => 1) (cmap J))
  rw [compress_sum, module_block_eq F N c hc hW hJ (Equiv.refl P4) (fun _ _ => rfl) y (μ f)
    hsite] at h2
  have hs : 0 < ∏ i, (c i)⁻¹ := Finset.prod_pos fun i _ => inv_pos.mpr (hc i)
  have h3 := (posSemidef_of_cmap h2).smul (inv_pos.mpr hs).le
  rwa [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h3

/-- **Item 5, word blocks.** Every compression `Bᵀ L B` (any real basis `B`) is PSD. -/
theorem wordBlock_posSemidef {d : ℕ} (hd : 4 ≤ d) {T : Finset (Fin 4)} (hT : IsCut T)
    {tab : P4 → P4 → P4 × ℕ} (htab : TabAt T d tab)
    {K : κ → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (F N : (i : κ) → P4 → Matrix (K i) (K i) ℝ) (hF : ∀ i, ModuleAt d tab (F i))
    (c : κ → ℝ) (hc : ∀ i, 0 < c i) (hW : ∀ i p, ∑ p', gram d p p' • N i p' = c i • F i p)
    {Kq : Type*} [Fintype Kq] [DecidableEq Kq] {Fq : P4 → Matrix Kq Kq ℝ}
    {J : Matrix (Fin 4 → Fin 2) Kq ℝ} (hJ : QubitAt T Fq J)
    {a b : (κ → Fin d) × Fin 2 → ℂ} {μ : Fam → Tup κ → ℝ} (hμ : IsMCoord a b μ) (f : Fam)
    {k : Type*} [Fintype k] (B : Matrix (((i : κ) → K i) × Kq) k ℝ) :
    (Bᵀ * blockOp N Fq (Equiv.refl P4) (μ f) * B).PosSemidef := by
  have := (blockOp_word_posSemidef hd hT htab F N hF c hc hW hJ hμ f).conjTranspose_mul_mul_same B
  rwa [conjTranspose_eq_transpose_of_trivial] at this

end Setup

end WernerEndpoint

end

#print axioms WernerEndpoint.posSemidef_of_cmap
#print axioms WernerEndpoint.cmap_posSemidef
#print axioms WernerEndpoint.moduleAt_of_verifier
#print axioms WernerEndpoint.phys_eq
#print axioms WernerEndpoint.weingarten_eq
#print axioms WernerEndpoint.module_block_eq
#print axioms WernerEndpoint.cp_sites
#print axioms WernerEndpoint.blockOp_word_posSemidef
#print axioms WernerEndpoint.wordBlock_posSemidef
