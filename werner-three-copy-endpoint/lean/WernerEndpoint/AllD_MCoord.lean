import WernerEndpoint.AllD_Gram
import WernerEndpoint.AllD_Embed

/-!
# All-d lemma chain: trace coordinates `m` (steps 1, 2, 4 and the d-dependence of step 5)

Coordinates are functions on diagram tuples `Tup κ = (κ → Perm (Fin 4)) × Perm (Fin 4)` (three
sites and the qubit; `t.1 i` is the site-`i` diagram, `t.2` the qubit diagram), one per family.

* `siteG d y u = ∑_s ∏_i G_d(u_i, s_i) · y(s, u_q)` is `(G_d^{⊗κ} ⊗ I) y`;
  `qubG dq μ u = ∑_q G_{dq}(u_q, q) · μ(u_s, q)` is `(I ⊗ G_{dq}) μ`.
* `IsMCoord a b μ`: `(I ⊗ G_2) μ_f = τ_f` for every family, where `τ_f = tExp f a b` are the
  permutation expectations of the twirled moments. This is the defining property of the trace
  coordinates `m = (G_d^{⊗3} ⊗ I) x` of `all_d/README.md`, stated without choosing a generalised
  inverse of `G_2`: any `μ` with this property works.
* `exists_mcoord` (**step 1**): at the native dimension, `μ_f = (G_d^{⊗κ} ⊗ I) x_f` with `x_f` the
  real orbit-invariant coefficients of `twirl_rep` has the property, and `μ` is invariant under
  the orbit generators of every family (`OrbInv`).
* `isMCoord_embVec` (**step 2**): the property is preserved by zero padding into any larger local
  space, so the **same** `μ` is a trace-coordinate vector of the padded lift at every `d ≥ e`.
* `mTr_eq`, `mObj_eq`, `mRowVal_eq` (**step 4**): every trace functional
  `∑ coef · Tr[(⊗P_w ⊗ P_wq) Ŷ_f]` is the `d`-free functional
  `∑ coef ∑_q 2^{cyc(wq q)} μ_f((w_i⁻¹), q)` of `μ` (the verifier's `mrow`); the objective
  `Tr[objective4 · Ŷ31] = q(C)` likewise. `RowValid` and `rowValid_trace`,
  `rowValid_contrast`, `rowValid_31_22`, `rowValid_22_13`: the verifier's four row families are
  physically valid in this form (**item 2** of the red team's list).
* `rep_of_mcoord` (**the only place `d ≥ 4` enters**): at `d ≥ 4`, if `μ` is a
  trace-coordinate vector of a lift then `y_f = (Wg_d^{⊗κ} ⊗ I) μ_f` is a real representation of
  the twirled moment, `Ŷ_f = ∑_t y_f(t) P_t`, with `(G_d^{⊗κ} ⊗ I) y_f = μ_f` (`G_d Wg_d = I`).
  For `e = 2, 3` points this is applied after padding into `d ≥ 4` (item 1).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section MCoord

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `(G_d^{⊗κ} ⊗ I) y`. -/
def siteG (d : ℕ) (y : Tup κ → ℝ) (u : Tup κ) : ℝ :=
  ∑ s : κ → P4, (∏ i, gram d (u.1 i) (s i)) * y (s, u.2)

/-- `(Wg_d^{⊗κ} ⊗ I) μ`. -/
def siteWg (d : ℕ) (μ : Tup κ → ℝ) (u : Tup κ) : ℝ :=
  ∑ s : κ → P4, (∏ i, wg d (u.1 i) (s i)) * μ (s, u.2)

/-- `(I ⊗ G_dq) μ`. -/
def qubG (dq : ℕ) (μ : Tup κ → ℝ) (u : Tup κ) : ℝ :=
  ∑ q : P4, gram dq u.2 q * μ (u.1, q)

/-- `(G_d^{⊗κ} ⊗ G_dq) y`. -/
def fullG (d dq : ℕ) (y : Tup κ → ℝ) (u : Tup κ) : ℝ :=
  ∑ t : Tup κ, y t * ((∏ i, gram d (u.1 i) (t.1 i)) * gram dq u.2 t.2)

theorem qubG_siteG (d dq : ℕ) (y : Tup κ → ℝ) (u : Tup κ) :
    qubG dq (siteG d y) u = fullG d dq y u := by
  simp only [qubG, siteG, fullG, Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `(G_d ⊗ ...)(Wg_d ⊗ ...) = I` on the sites, for `d ≥ 4`. -/
theorem siteG_siteWg {d : ℕ} (hd : 4 ≤ d) (μ : Tup κ → ℝ) : siteG d (siteWg d μ) = μ := by
  funext u
  simp only [siteG, siteWg, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hGW : ∀ p r : P4, ∑ s, gram d p s * wg d s r = if p = r then 1 else 0 := by
    intro p r
    have := congrFun (congrFun (gram_mul_wg hd) p) r
    simpa [Matrix.mul_apply, gramMat, Matrix.one_apply] using this
  have : ∀ r : κ → P4, ∑ s : κ → P4, (∏ i, gram d (u.1 i) (s i)) * ((∏ i, wg d (s i) (r i)) *
      μ (r, u.2)) = (∏ i, if u.1 i = r i then (1 : ℝ) else 0) * μ (r, u.2) := by
    intro r
    simp_rw [← hGW, Fintype.prod_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  simp only [this, Fintype.prod_boole]
  rw [Finset.sum_eq_single u.1]
  · simp
  · intro r _ hr
    rw [if_neg]; · ring
    intro h; exact hr (funext fun i => (h i).symm)
  · intro h; exact absurd (Finset.mem_univ _) h

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-- The trace formula against a real representation, in Gram form. -/
theorem trace_inv_permOp_rep (x : Tup κ → ℝ) (u : Tup κ) :
    (permOp ι ρ (fun i => (u.1 i)⁻¹) (u.2)⁻¹ * ∑ t, ((x t : ℝ) : ℂ) • permOp ι ρ t.1 t.2).trace =
      ((fullG (Fintype.card ι) (Fintype.card ρ) x u : ℝ) : ℂ) := by
  rw [Matrix.mul_sum, Matrix.trace_sum, fullG]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, trace_permOp_mul_permOp, smul_eq_mul]
  simp only [gram]
  push_cast
  ring

/-- Trace coordinates of a lift (`(I ⊗ G_{|ρ|}) μ_f = τ_f` for every family). -/
def IsMCoord (a b : (κ → ι) × ρ → ℂ) (μ : Fam → Tup κ → ℝ) : Prop :=
  ∀ f u, qubG (Fintype.card ρ) (μ f) u = tExp f a b u

/-- Invariance under the orbit generators of every family. -/
def OrbInv (κ : Type*) [Fintype κ] [DecidableEq κ] (m : Fam → Tup κ → ℝ) : Prop :=
  ∀ f, ∀ ψ ∈ orbitGens κ f, ∀ t, m f (ψ t) = m f t

theorem tExp_of_rep {f : Fam} {a b : (κ → ι) × ρ → ℂ} {x : Tup κ → ℝ}
    (hx : twirl f a b = ∑ t, ((x t : ℝ) : ℂ) • permOp ι ρ t.1 t.2) (u : Tup κ) :
    tExp f a b u = fullG (Fintype.card ι) (Fintype.card ρ) x u := by
  rw [tExp, hx, trace_inv_permOp_rep, Complex.ofReal_re]

/-! ### Orbit invariance of `(G ⊗ I) x` -/

theorem siteG_reindex (d : ℕ) (x : Tup κ → ℝ) (u u' : Tup κ) (φ : P4 ≃ P4)
    (hg : ∀ i p, gram d (u.1 i) p = gram d (u'.1 i) (φ p))
    (hx : ∀ s : κ → P4, x (s, u.2) = x (fun i => φ (s i), u'.2)) :
    siteG d x u = siteG d x u' := by
  unfold siteG
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => φ) _ _ fun s => ?_
  simp only [Equiv.piCongrRight_apply, hg, hx]
  rfl

theorem siteG_sitePermT (d : ℕ) {x : Tup κ → ℝ} (π : Equiv.Perm κ)
    (hx : ∀ t, x (sitePermT π t) = x t) (u : Tup κ) :
    siteG d x (sitePermT π u) = siteG d x u := by
  unfold siteG
  let e : (κ → P4) ≃ (κ → P4) :=
    { toFun := fun s i => s (π.symm i)
      invFun := fun s i => s (π i)
      left_inv := fun s => funext fun i => by simp
      right_inv := fun s => funext fun i => by simp }
  refine Fintype.sum_equiv e _ _ fun s => ?_
  have h1 := hx (fun i => s (π.symm i), u.2)
  simp only [sitePermT, Equiv.coe_fn_mk, Equiv.symm_apply_apply] at h1
  have hp : ∏ i, gram d (u.1 i) (s (π.symm i)) = ∏ i, gram d (u.1 (π i)) (s i) := by
    rw [← Equiv.prod_comp π]; simp only [Equiv.symm_apply_apply]
  simp only [sitePermT, Equiv.coe_fn_mk, e]
  rw [hp, ← h1]

theorem siteG_invT (d : ℕ) {x : Tup κ → ℝ} (hx : ∀ t, x (invT t) = x t) (u : Tup κ) :
    siteG d x (invT u) = siteG d x u := by
  refine siteG_reindex d x _ u (Equiv.inv P4) (fun i p => ?_) (fun s => ?_)
  · simp only [invT, Equiv.coe_fn_mk, Equiv.inv_apply]
    rw [← gram_inv d (u.1 i) p⁻¹, inv_inv]
  · have h1 := hx (fun i => (s i)⁻¹, u.2)
    simp only [invT, Equiv.coe_fn_mk, inv_inv] at h1 ⊢
    exact h1

theorem siteG_lmulT (d : ℕ) {x : Tup κ → ℝ} (g : P4) (hx : ∀ t, x (lmulT g t) = x t)
    (u : Tup κ) : siteG d x (lmulT g u) = siteG d x u := by
  refine siteG_reindex d x _ u (Equiv.mulLeft g⁻¹) (fun i p => ?_) (fun s => ?_)
  · simp only [lmulT, Equiv.coe_fn_mk, Equiv.coe_mulLeft]
    rw [← gram_lmul d g (u.1 i) (g⁻¹ * p), mul_inv_cancel_left]
  · have h1 := hx (fun i => g⁻¹ * s i, u.2)
    simp only [lmulT, Equiv.coe_fn_mk, mul_inv_cancel_left] at h1 ⊢
    exact h1

theorem siteG_rmulT (d : ℕ) {x : Tup κ → ℝ} (g : P4) (hx : ∀ t, x (rmulT g t) = x t)
    (u : Tup κ) : siteG d x (rmulT g u) = siteG d x u := by
  refine siteG_reindex d x _ u (Equiv.mulRight g⁻¹) (fun i p => ?_) (fun s => ?_)
  · simp only [rmulT, Equiv.coe_fn_mk, Equiv.coe_mulRight]
    rw [← gram_rmul d g (u.1 i) (p * g⁻¹), inv_mul_cancel_right]
  · have h1 := hx (fun i => s i * g⁻¹, u.2)
    simp only [rmulT, Equiv.coe_fn_mk, inv_mul_cancel_right] at h1 ⊢
    exact h1

/-- **Step 1.** At the native dimension the twirled moments have trace coordinates
`μ_f = (G_{|ι|}^{⊗κ} ⊗ I) x_f`, invariant under every family's orbit generators. -/
theorem exists_mcoord (a b : (κ → ι) × ρ → ℂ) :
    ∃ μ : Fam → Tup κ → ℝ, IsMCoord a b μ ∧ OrbInv κ μ := by
  choose x hx hπ hinv hl hr using fun f => twirl_rep (ι := ι) (ρ := ρ) f a b
  refine ⟨fun f => siteG (Fintype.card ι) (x f), fun f u => ?_, fun f ψ hψ t => ?_⟩
  · rw [qubG_siteG, tExp_of_rep (hx f)]
  · rcases hψ with ((⟨π, rfl⟩ | hinv') | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩
    · exact siteG_sitePermT _ π (hπ f π) t
    · rw [Set.mem_singleton_iff] at hinv'; subst hinv'
      exact siteG_invT _ (hinv f) t
    · exact siteG_lmulT _ g (hl f g hg) t
    · exact siteG_rmulT _ g (hr f g hg) t

/-- **Step 2.** Zero padding into a larger local space keeps every trace-coordinate vector. -/
theorem isMCoord_embVec {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι ↪ ι')
    {a b : (κ → ι) × ρ → ℂ} {μ : Fam → Tup κ → ℝ} (h : IsMCoord a b μ) :
    IsMCoord (embVec e a) (embVec e b) μ := by
  intro f u
  rw [h f u, tExp_embVec]

/-! ### Step 4: rows and objective are `d`-free functionals of `μ` -/

/-- The trace functional `Tr[(⊗P_w ⊗ P_wq) Ŷ]` in trace coordinates:
`∑_q G_dq(wq⁻¹, q) μ((w_i⁻¹), q) = ∑_q dq^{cyc(wq q)} μ((w_i⁻¹), q)` (the verifier's `mrow`). -/
def mTr (dq : ℕ) (w : Tup κ) (μ : Tup κ → ℝ) : ℝ :=
  ∑ q : P4, gram dq (w.2)⁻¹ q * μ (fun i => (w.1 i)⁻¹, q)

theorem mTr_eq {a b : (κ → ι) × ρ → ℂ} {μ : Fam → Tup κ → ℝ} (h : IsMCoord a b μ) (f : Fam)
    (w : Tup κ) : mTr (Fintype.card ρ) w (μ f) = (permOp ι ρ w.1 w.2 * twirl f a b).trace.re := by
  have := h f (fun i => (w.1 i)⁻¹, (w.2)⁻¹)
  simp only [qubG, tExp, inv_inv] at this
  rw [← this]
  rfl

theorem trace_permOp_twirl_im {f : Fam} {a b : (κ → ι) × ρ → ℂ} (w : Tup κ) :
    (permOp ι ρ w.1 w.2 * twirl f a b).trace.im = 0 := by
  obtain ⟨x, hx, -⟩ := twirl_rep (ι := ι) (ρ := ρ) f a b
  have := trace_inv_permOp_rep (ι := ι) (ρ := ρ) x (fun i => (w.1 i)⁻¹, (w.2)⁻¹)
  simp only [inv_inv] at this
  rw [hx, this, Complex.ofReal_im]

/-- The objective `Tr[objective4 · Ŷ31]` in trace coordinates. -/
def mObj (dq : ℕ) (μ : Fam → Tup κ → ℝ) : ℝ :=
  ∑ S : Finset κ, (-1 / 2 : ℝ) ^ S.card * mTr dq (objSites S, Equiv.swap 0 3) (μ .f31)

theorem mObj_eq_trace {a b : (κ → ι) × ρ → ℂ} {μ : Fam → Tup κ → ℝ} (h : IsMCoord a b μ) :
    mObj (Fintype.card ρ) μ = (objective4 κ ι ρ * twirl .f31 a b).trace.re := by
  simp only [mObj, mTr_eq h, objective4, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [show ((-1 / 2 : ℂ) ^ S.card) = (((-1 / 2 : ℝ) ^ S.card : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **Step 4, objective.** For a lift, the `d`-free objective functional is `q(C)`. -/
theorem mObj_eq {a b : (κ → ι) × ρ → ℂ} {μ : Fam → Tup κ → ℝ} (h : IsMCoord a b μ)
    (hab : IsLift a b) : mObj (Fintype.card ρ) μ = qfun (liftC a b) := by
  rw [mObj_eq_trace h, twirl_objective hab, Complex.ofReal_re]

/-- A row: a list of terms `(coef, family, word)`, read as `∑ coef · Tr[(⊗P_w ⊗ P_wq) Ŷ_fam]`. -/
abbrev Row (κ : Type*) := List (ℝ × Fam × Tup κ)

/-- The row in trace coordinates. -/
def mRowVal (dq : ℕ) (r : Row κ) (μ : Fam → Tup κ → ℝ) : ℝ :=
  (r.map fun c => c.1 * mTr dq c.2.2 (μ c.2.1)).sum

/-- The row on the twirled moments of a lift. -/
def pRowVal (r : Row κ) (a b : (κ → ι) × ρ → ℂ) : ℝ :=
  (r.map fun c => c.1 * (permOp ι ρ c.2.2.1 c.2.2.2 * twirl c.2.1 a b).trace.re).sum

theorem mRowVal_eq {a b : (κ → ι) × ρ → ℂ} {μ : Fam → Tup κ → ℝ} (h : IsMCoord a b μ)
    (r : Row κ) : mRowVal (Fintype.card ρ) r μ = pRowVal r a b := by
  simp only [mRowVal, pRowVal, mTr_eq h]

/-- **Physical validity of a row**: on the twirled moments of every lift, in every local
dimension `e`, the row takes the value `v` (`0` for the homogeneous rows, the trace value for
the trace row). -/
def RowValid (κ : Type*) [Fintype κ] [DecidableEq κ] (r : Row κ) (v : ℝ) : Prop :=
  ∀ (e : ℕ) (a b : (κ → Fin e) × Fin 2 → ℂ), IsLift a b → pRowVal r a b = v

/-! ### Item 2: the verifier's four row families are physically valid -/

theorem pRowVal_two (c₁ c₂ : ℝ) (f₁ f₂ : Fam) (w₁ w₂ : κ → P4) (q₁ q₂ : P4)
    (a b : (κ → ι) × ρ → ℂ) :
    pRowVal [(c₁, f₁, (w₁, q₁)), (c₂, f₂, (w₂, q₂))] a b =
      (((c₁ : ℂ) * (permOp ι ρ w₁ q₁ * twirl f₁ a b).trace +
        (c₂ : ℂ) * (permOp ι ρ w₂ q₂ * twirl f₂ a b).trace)).re := by
  simp [pRowVal]

/-- Trace row (`ROWDEF[0]`, scaled by `c`): `c · Tr Ŷ31 = c`. -/
theorem rowValid_trace (c : ℝ) :
    RowValid κ [(c, .f31, ((fun _ => (1 : P4)), (1 : P4)))] c := by
  intro e a b hab
  simp only [pRowVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [permOp_one, Matrix.one_mul, twirl_trace hab, Complex.one_re, mul_one]

/-- Contrast rows (`2 Tr[P_(w,wq) Ŷ_f] − c Tr[P_(w, removeSlot wq r) Ŷ_f] = 0`). -/
theorem rowValid_contrast (f : Fam) (r : Fin 4) (hr : famPat f r = false)
    (w : κ → P4) (wq : P4) (hw : ∀ i, w i r = r) :
    RowValid κ [(2, f, (w, wq)), (-(if wq r = r then 2 else 1), f, (w, removeSlot wq r))] 0 := by
  intro e a b hab
  rw [pRowVal_two]
  have h := twirl_contrast_row f r hr w wq hw (Fintype.card_fin 2) hab
  have e1 : ((-(if wq r = r then (2 : ℝ) else 1) : ℝ) : ℂ) = -(if wq r = r then 2 else 1) := by
    split_ifs <;> push_cast <;> ring
  rw [e1, show ((2 : ℝ) : ℂ) = 2 by norm_num, h]
  ring_nf
  simp

/-- 31–22 rows (every component fixes slot 2). -/
theorem rowValid_31_22 (w : κ → P4) (wq : P4) (hw : ∀ i, w i 2 = 2) (hq : wq 2 = 2) :
    RowValid κ [(2, .f31, (w, wq)), (-2, .f22, (w, wq))] 0 := by
  intro e a b hab
  rw [pRowVal_two, twirl_row_31_22 w wq hw hq hab]
  push_cast
  ring_nf
  simp

/-- 22–13 rows (every component fixes slot 1; `π = PI_ABB`). -/
theorem rowValid_22_13 (w : κ → P4) (wq : P4) (hw : ∀ i, w i 1 = 1) (hq : wq 1 = 1) :
    RowValid κ [(2, .f22, (w, wq)),
      (-2, .f13, (fun i => piABB * w i * piABB⁻¹, piABB * wq * piABB⁻¹))] 0 := by
  intro e a b hab
  rw [pRowVal_two, twirl_row_22_13 w wq hw hq hab]
  push_cast
  ring_nf
  simp

/-! ### The representation at `d ≥ 4` -/

theorem hs_permOp_inv (u : Tup κ) (Z : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ) :
    hs (permOp ι ρ u.1 u.2) Z = (permOp ι ρ (fun i => (u.1 i)⁻¹) (u.2)⁻¹ * Z).trace := by
  rw [hs_eq_trace, permOp_conjTranspose]

theorem fullG_sub (d dq : ℕ) (y x : Tup κ → ℝ) (u : Tup κ) :
    fullG d dq (fun t => y t - x t) u = fullG d dq y u - fullG d dq x u := by
  simp only [fullG, sub_mul, Finset.sum_sub_distrib]

theorem hs_sum_left {n β : Type*} [Fintype n] [DecidableEq n] [Fintype β] (c : β → ℂ)
    (A : β → Matrix n n ℂ) (B : Matrix n n ℂ) :
    hs (∑ t, c t • A t) B = ∑ t, star (c t) * hs (A t) B := by
  simp only [hs_eq_trace, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- **The `d ≥ 4` step.** If `μ` is a trace-coordinate vector of a lift at local dimension
`d ≥ 4`, then `y_f = (Wg_d^{⊗κ} ⊗ I) μ_f` represents the twirled moment, and
`(G_d^{⊗κ} ⊗ I) y_f = μ_f`. -/
theorem rep_of_mcoord {d : ℕ} (hd : 4 ≤ d) {a b : (κ → Fin d) × ρ → ℂ} {μ : Fam → Tup κ → ℝ}
    (h : IsMCoord a b μ) (f : Fam) :
    twirl f a b = ∑ t, ((siteWg d (μ f) t : ℝ) : ℂ) • permOp (Fin d) ρ t.1 t.2 ∧
      siteG d (siteWg d (μ f)) = μ f := by
  refine ⟨?_, siteG_siteWg hd (μ f)⟩
  obtain ⟨x, hx, -⟩ := twirl_rep (ι := Fin d) (ρ := ρ) f a b
  have key : ∀ u : Tup κ,
      fullG d (Fintype.card ρ) (siteWg d (μ f)) u = fullG d (Fintype.card ρ) x u := by
    intro u
    have := h f u
    rw [tExp_of_rep hx, Fintype.card_fin] at this
    rw [← qubG_siteG, siteG_siteWg hd, this]
  let c : Tup κ → ℂ := fun t => ((siteWg d (μ f) t - x t : ℝ) : ℂ)
  let D : Matrix (Fin 4 → (κ → Fin d) × ρ) (Fin 4 → (κ → Fin d) × ρ) ℂ :=
    ∑ t, c t • permOp (Fin d) ρ t.1 t.2
  have hpair : ∀ u : Tup κ, hs (permOp (Fin d) ρ u.1 u.2) D = 0 := by
    intro u
    rw [hs_permOp_inv, trace_inv_permOp_rep, Fintype.card_fin, fullG_sub, key, sub_self,
      Complex.ofReal_zero]
  have hDD : hs D D = 0 := by
    conv_lhs => arg 1; rw [show D = ∑ t, c t • permOp (Fin d) ρ t.1 t.2 from rfl]
    rw [hs_sum_left]
    exact Finset.sum_eq_zero fun t _ => by rw [hpair t, mul_zero]
  have hD : D = 0 := hs_self_eq_zero.mp hDD
  have : D = (∑ t, ((siteWg d (μ f) t : ℝ) : ℂ) • permOp (Fin d) ρ t.1 t.2) - twirl f a b := by
    simp only [D, c, hx, ← Finset.sum_sub_distrib, Complex.ofReal_sub, sub_smul]
  rw [hD] at this
  exact (sub_eq_zero.mp this.symm).symm

end MCoord

end WernerEndpoint

end

#print axioms WernerEndpoint.qubG_siteG
#print axioms WernerEndpoint.siteG_siteWg
#print axioms WernerEndpoint.trace_inv_permOp_rep
#print axioms WernerEndpoint.exists_mcoord
#print axioms WernerEndpoint.isMCoord_embVec
#print axioms WernerEndpoint.mTr_eq
#print axioms WernerEndpoint.mObj_eq
#print axioms WernerEndpoint.mRowVal_eq
#print axioms WernerEndpoint.rowValid_trace
#print axioms WernerEndpoint.rowValid_contrast
#print axioms WernerEndpoint.rowValid_31_22
#print axioms WernerEndpoint.rowValid_22_13
#print axioms WernerEndpoint.rep_of_mcoord
