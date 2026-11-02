import LayerDT0.Poly
import LayerDT0.Tables
import LayerDProto.PDSound
import LayerDProto.TraceRows

/-!
# Layer D (t = 0): the site modules (`SiteCert` for every `d ≥ 4`)

A site module is given by integer coefficient lists (`SiteData`): `F(p)(d)` (24 matrices, in `d`),
an adjugate `A(d)` and `δ(d)` of `F(e)`, the `t`-polynomials `N(p)(t)`, the exponent `e = α + 4`,
a constant lower-triangular congruence `W`, coefficient bounds and the Kronecker width `β`.

`siteChk` checks, by integer arithmetic at `X = 2^β` and on the lists:

* (A2) `F(p)ᵀ = F(p⁻¹)`; `F(e) A = δ 1`; `F(p) A F(q) = X^{L p q} δ F(S p q)` for all `p, q`;
* (A3) `W F(e) Wᵀ` is strictly diagonally dominant for every `d ≥ 4` and `δ(d) > 0` for every
  `d ≥ 4` (leading-term dominance, `domPos`);
* (A4) `∑_{p'} X^{cyc(p⁻¹p')} rev₆(N(p'))(X) = R(X) X^e F(p)(X)` with `R(d) = (d²-1)(d²-4)(d²-9)`
  (`= d⁶ den(1/d)`), i.e. the verifier's Laurent identity times `d⁶`;
* the coefficient bounds of the data, and `2 B < X` for the a priori bound `B` of each identity.

**`siteCert_of_chk`**: a passing check gives `SiteCert (tabOf S L) (NP k Nl)`, with
`c(d) = R(d) dᵉ / d⁶ > 0`.
-/

open Matrix Polynomial Finset

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint

/-! ### Data -/

def f4 (l : List (List (List (List ℤ)))) (i a b : ℕ) : List ℤ := ((l.getD i []).getD a []).getD b []
def f3 (l : List (List (List ℤ))) (a b : ℕ) : List ℤ := (l.getD a []).getD b []

structure SiteData where
  k : ℕ
  F : List (List (List (List ℤ)))
  A : List (List (List ℤ))
  δ : List ℤ
  N : List (List (List (List ℤ)))
  e : ℕ
  W : List (List ℤ)
  MF : ℤ
  DF : ℕ
  MA : ℤ
  DA : ℕ
  Md : ℤ
  Dd : ℕ
  MN : ℤ
  β : ℕ

/-- `R(d) = d⁶ den(1/d) = (d² − 1)(d² − 4)(d² − 9)`. -/
def Rl : List ℤ := [-36, 0, 49, 0, -14, 0, 1]

/-- The index of `(permTab i)⁻¹ * permTab j`. -/
def mulInvIdx (i j : ℕ) : ℕ := permIdx ((permTab (fin24 i))⁻¹ * permTab (fin24 j))

/-- The index of `(permTab i)⁻¹`. -/
def invIdx (i : ℕ) : ℕ := permIdx (permTab (fin24 i))⁻¹

/-! ### The check -/

section Check
variable (s : SiteData)

def SiteData.X : ℤ := 2 ^ s.β
def SiteData.FX (i a b : ℕ) : ℤ := horner s.X (f4 s.F i a b)
def SiteData.AX (a b : ℕ) : ℤ := horner s.X (f3 s.A a b)

def SiteData.Bhom : ℤ := s.k * (s.k * ((s.DF + s.DA) * ((s.DF * (s.MF * s.MA)) * s.MF))) + s.Dd * (s.Md * s.MF)
def SiteData.Bwg : ℤ := 24 * s.MN + 7 * (49 * s.MF)
def SiteData.Badj : ℤ := s.k * (s.DF * (s.MF * s.MA)) + s.Md

def rng (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f
def lsum (n : ℕ) (f : ℕ → ℤ) : ℤ := ((List.range n).map f).sum

def SiteData.bndOK : Bool :=
  decide (0 ≤ s.MF) && decide (0 ≤ s.MA) && decide (0 ≤ s.Md) && decide (0 ≤ s.MN) &&
  rng 24 (fun i => rng s.k fun a => rng s.k fun b =>
    bndL s.MF s.DF (f4 s.F i a b) && decide ((f4 s.N i a b).length ≤ 7) &&
      bndL s.MN 7 (rev 6 (f4 s.N i a b))) &&
  rng s.k (fun a => rng s.k fun b => bndL s.MA s.DA (f3 s.A a b)) && bndL s.Md s.Dd s.δ &&
  decide (2 * s.Bhom < s.X) && decide (2 * s.Bwg < s.X) && decide (2 * s.Badj < s.X)

def SiteData.transOK : Bool :=
  rng 24 fun i => rng s.k fun a => rng s.k fun b => f4 s.F (invIdx i) b a == f4 s.F i a b

def SiteData.adjOK : Bool :=
  rng s.k fun a => rng s.k fun b =>
    lsum s.k (fun t => s.FX 0 a t * s.AX t b) == (if a = b then horner s.X s.δ else 0)

/-- (A2), row `i`. -/
def SiteData.homRow (S L : List (List ℕ)) (i : ℕ) : Bool :=
  rng 24 fun j => rng s.k fun a => rng s.k fun b =>
    lsum s.k (fun t => lsum s.k fun u => s.FX i a t * s.AX t u * s.FX j u b) ==
      s.X ^ n2 L i j * (horner s.X s.δ * s.FX (tS S i j).val a b)

/-- (A4), row `i`. -/
def SiteData.wgRow (i : ℕ) : Bool :=
  rng s.k fun a => rng s.k fun b =>
    lsum 24 (fun j => s.X ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) * horner s.X (rev 6 (f4 s.N j a b))) ==
      horner s.X Rl * (s.X ^ s.e * s.FX i a b)

def SiteData.wE (a b : ℕ) : ℤ := (s.W.getD a []).getD b 0

def plsum (ls : List (List ℤ)) : List ℤ := ls.foldr padd []

/-- `(W F(e) Wᵀ)_{ab}` as a coefficient list. -/
def SiteData.El (a b : ℕ) : List ℤ :=
  plsum ((List.range s.k).map fun t => plsum ((List.range s.k).map fun u =>
    psmul (s.wE a t * s.wE b u) (f4 s.F 0 t u)))

def SiteData.domRow (a : ℕ) : List ℤ :=
  padd (s.El a a) (psmul (-1) (plsum ((List.range s.k).map fun b => if b = a then [] else pabs (s.El a b))))

def SiteData.pdOK : Bool :=
  domPos s.δ && rng s.k (fun a => domPos (s.domRow a)) &&
  rng s.k (fun a => rng s.k fun b => decide (a < b → s.wE a b = 0) && decide (a = b → 0 < s.wE a b))

end Check

/-! ### Realisation -/

/-- **The site `t`-polynomials** `N(p)(t)` of a module, as `BlockSpec.N`. -/
noncomputable def NP (k : ℕ) (Nl : List (List (List (List ℤ)))) : P4 → Matrix (Fin k) (Fin k) ℝ[X] :=
  fun p => Matrix.of fun a b => (toP (f4 Nl (permIdx p) a b)).map (Int.castRingHom ℝ)

noncomputable def SiteData.FR (s : SiteData) (x : ℝ) (i : ℕ) : Matrix (Fin s.k) (Fin s.k) ℝ :=
  Matrix.of fun a b => ev x (f4 s.F i a b)

noncomputable def SiteData.AR (s : SiteData) (x : ℝ) : Matrix (Fin s.k) (Fin s.k) ℝ :=
  Matrix.of fun a b => ev x (f3 s.A a b)

/-! ### Generic facts -/

theorem rng_spec {n : ℕ} {f : ℕ → Bool} (h : rng n f = true) {i : ℕ} (hi : i < n) : f i = true :=
  all_range h hi

theorem lsum_eq' (n : ℕ) (f : ℕ → ℤ) : lsum n f = ∑ i ∈ range n, f i := lsum_eq f n

theorem permIdx_lt (p : P4) : permIdx p < 24 := by
  obtain ⟨i, rfl⟩ := permTab_surj p
  rw [permIdx_permTab]; exact i.isLt

theorem permTab_permIdx (p : P4) : permTab (fin24 (permIdx p)) = p := by
  obtain ⟨i, rfl⟩ := permTab_surj p
  rw [permIdx_permTab, fin24_val]

theorem permIdx_one : permIdx 1 = 0 := by decide

theorem ev_toP_eval₂ (x : ℝ) (l : List ℤ) : (toP l).eval₂ (Int.castRingHom ℝ) x = ev x l := rfl

theorem CB_sum_range (n : ℕ) {f : ℕ → ℤ[X]} {M : ℤ} {D : ℕ} (hM : 0 ≤ M)
    (h : ∀ i < n, CB (f i) M D) : CB (∑ i ∈ range n, f i) (n * M) D := by
  have := CB_sum (range n) hM fun i hi => h i (mem_range.mp hi)
  rwa [card_range] at this

/-- Two integer polynomials with bounded coefficients, equal at one large point, are equal at
every real point. -/
theorem ev_eq_of_kron {P Q : ℤ[X]} {M M' : ℤ} {D D' : ℕ} (hP : CB P M D) (hQ : CB Q M' D') {x : ℤ}
    (hx : 2 * (M + M') < x) (h : P.eval x = Q.eval x) (y : ℝ) :
    P.eval₂ (Int.castRingHom ℝ) y = Q.eval₂ (Int.castRingHom ℝ) y := by
  have := eq_zero_of_CB_eval (CB_sub hP hQ) hx (by rw [eval_sub, h, sub_self])
  rw [sub_eq_zero.mp this]

theorem sum_fin_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i : Fin n, f i = ∑ i ∈ range n, f i := Fin.sum_univ_eq_sum_range f n

/-! ### Soundness -/

section Sound
variable {s : SiteData}

theorem bnd_parts (hb : s.bndOK = true) :
    0 ≤ s.MF ∧ 0 ≤ s.MA ∧ 0 ≤ s.Md ∧ 0 ≤ s.MN ∧
    (∀ i < 24, ∀ a < s.k, ∀ b < s.k, bndL s.MF s.DF (f4 s.F i a b) = true ∧
      (f4 s.N i a b).length ≤ 7 ∧ bndL s.MN 7 (rev 6 (f4 s.N i a b)) = true) ∧
    (∀ a < s.k, ∀ b < s.k, bndL s.MA s.DA (f3 s.A a b) = true) ∧ bndL s.Md s.Dd s.δ = true ∧
    2 * s.Bhom < s.X ∧ 2 * s.Bwg < s.X ∧ 2 * s.Badj < s.X := by
  simp only [SiteData.bndOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hb
  refine ⟨h1, h2, h3, h4, fun i hi a ha b hb => ?_, fun a ha b hb => rng_spec (rng_spec h6 ha) hb,
    h7, h8, h9, h10⟩
  have := rng_spec (rng_spec (rng_spec h5 hi) ha) hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem CB_F (hb : s.bndOK = true) {i a b : ℕ} (hi : i < 24) (ha : a < s.k) (hb' : b < s.k) :
    CB (toP (f4 s.F i a b)) s.MF s.DF :=
  CB_of_bndL (bnd_parts hb).1 ((bnd_parts hb).2.2.2.2.1 i hi a ha b hb').1

theorem CB_A (hb : s.bndOK = true) {a b : ℕ} (ha : a < s.k) (hb' : b < s.k) :
    CB (toP (f3 s.A a b)) s.MA s.DA :=
  CB_of_bndL (bnd_parts hb).2.1 ((bnd_parts hb).2.2.2.2.2.1 a ha b hb')

theorem CB_d (hb : s.bndOK = true) : CB (toP s.δ) s.Md s.Dd :=
  CB_of_bndL (bnd_parts hb).2.2.1 (bnd_parts hb).2.2.2.2.2.2.1

theorem eval_FX (i a b : ℕ) : (toP (f4 s.F i a b)).eval s.X = s.FX i a b := eval_toP _ _
theorem eval_AX (a b : ℕ) : (toP (f3 s.A a b)).eval s.X = s.AX a b := eval_toP _ _

/-- (A2) at every real point. -/
theorem hom_real {S L : List (List ℕ)} (hb : s.bndOK = true) (hh : ∀ i : Fin 24, s.homRow S L i = true)
    {i j : ℕ} (hi : i < 24) (hj : j < 24) (x : ℝ) :
    s.FR x i * s.AR x * s.FR x j = (x ^ n2 L i j * ev x s.δ) • s.FR x (tS S i j).val := by
  ext a b
  have hrow := rng_spec (rng_spec (rng_spec (hh ⟨i, hi⟩) hj) a.isLt) b.isLt
  rw [beq_iff_eq] at hrow
  set M3 : ℤ := (s.DF + s.DA) * ((s.DF * (s.MF * s.MA)) * s.MF) with hM3def
  have hterm : ∀ t < s.k, ∀ u < s.k,
      CB (toP (f4 s.F i a t) * toP (f3 s.A t u) * toP (f4 s.F j u b)) M3 (s.DF + s.DA + s.DF) := by
    intro t ht u hu
    have := CB_mul (CB_mul (CB_F hb hi a.isLt ht) (CB_A hb ht hu)) (CB_F hb hj hu b.isLt)
    rw [hM3def]; push_cast at this ⊢; exact this
  have hM3 : 0 ≤ M3 := by
    rcases Nat.eq_zero_or_pos s.k with h0 | h0
    · have := a.isLt; omega
    · exact (hterm 0 h0 0 h0).nonneg
  have hP := CB_sum_range s.k (by positivity) fun t ht =>
    CB_sum_range s.k hM3 fun u hu => hterm t ht u hu
  have hQ : CB (X ^ n2 L i j * (toP s.δ * toP (f4 s.F (tS S i j).val a b))) (s.Dd * (s.Md * s.MF))
      (s.Dd + s.DF + n2 L i j) :=
    CB_X_pow_mul (CB_mul (CB_d hb) (CB_F hb (tS S i j).isLt a.isLt b.isLt)) _
  have hx : 2 * (s.k * (s.k * M3) + s.Dd * (s.Md * s.MF)) < s.X := (bnd_parts hb).2.2.2.2.2.2.2.1
  have key := ev_eq_of_kron hP hQ hx (by
    simp only [eval_finset_sum, eval_mul, eval_pow, eval_X, eval_FX, eval_AX]
    simpa [lsum_eq', SiteData.FX, SiteData.AX, eval_toP] using hrow) x
  simp only [eval₂_finset_sum, eval₂_mul, eval₂_X_pow, ev_toP_eval₂] at key
  have lhs : (s.FR x i * s.AR x * s.FR x j) a b = ∑ t ∈ range s.k, ∑ u ∈ range s.k,
      ev x (f4 s.F i a t) * ev x (f3 s.A t u) * ev x (f4 s.F j u b) := by
    simp only [SiteData.FR, SiteData.AR, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← sum_fin_range s.k (fun t => ∑ u ∈ range s.k, ev x (f4 s.F i a t) * ev x (f3 s.A t u) *
      ev x (f4 s.F j u b))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← sum_fin_range s.k (fun u => ev x (f4 s.F i a t) * ev x (f3 s.A t u) * ev x (f4 s.F j u b))]
  rw [lhs, key]
  simp only [SiteData.FR, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem adj_real (hb : s.bndOK = true) (ha : s.adjOK = true) (x : ℝ) :
    s.FR x 0 * s.AR x = ev x s.δ • (1 : Matrix (Fin s.k) (Fin s.k) ℝ) := by
  ext a b
  have hrow := rng_spec (rng_spec ha a.isLt) b.isLt
  rw [beq_iff_eq] at hrow
  set M2 : ℤ := s.DF * (s.MF * s.MA) with hM2
  have hterm : ∀ t < s.k, CB (toP (f4 s.F 0 a t) * toP (f3 s.A t b)) M2 (s.DF + s.DA) :=
    fun t ht => CB_mul (CB_F hb (by norm_num) a.isLt ht) (CB_A hb ht b.isLt)
  have hP := CB_sum_range s.k (hterm 0 (by have := a.isLt; omega)).nonneg hterm
  have hQ : CB (if (a : ℕ) = b then toP s.δ else 0) s.Md s.Dd := by
    split_ifs
    · exact CB_d hb
    · exact ⟨fun i => by simpa using (bnd_parts hb).2.2.1, fun i _ => by simp⟩
  have hx : 2 * (s.k * M2 + s.Md) < s.X := (bnd_parts hb).2.2.2.2.2.2.2.2.2
  have key := ev_eq_of_kron hP hQ hx (by
    simp only [eval_finset_sum, eval_mul, eval_FX, eval_AX]
    rw [← lsum_eq', hrow]
    split_ifs <;> simp [eval_toP]) x
  simp only [eval₂_finset_sum, eval₂_mul, ev_toP_eval₂] at key
  simp only [SiteData.FR, SiteData.AR, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [sum_fin_range s.k (fun t => ev x (f4 s.F 0 a t) * ev x (f3 s.A t b)), key]
  by_cases h : a = b
  · subst h; simp [ev_toP_eval₂]
  · have : (a : ℕ) ≠ b := fun e => h (Fin.ext e)
    simp [h, this]

theorem trans_real (ht : s.transOK = true) {i : ℕ} (hi : i < 24) (x : ℝ) :
    (s.FR x i)ᵀ = s.FR x (invIdx i) := by
  ext a b
  have := rng_spec (rng_spec (rng_spec ht hi) b.isLt) a.isLt
  rw [beq_iff_eq] at this
  simp only [SiteData.FR, Matrix.transpose_apply, Matrix.of_apply, this]

theorem cycTab_le : ∀ m : Fin 24, LayerDProto.cycTab m ≤ 4 := by decide

theorem ev_Rl (x : ℝ) : ev x Rl = (x ^ 2 - 1) * (x ^ 2 - 4) * (x ^ 2 - 9) := by
  simp only [Rl, ev_cons, ev_nil]; push_cast; ring

theorem ev_Rl_pos {x : ℝ} (hx : 4 ≤ x) : 0 < ev x Rl := by
  rw [ev_Rl]
  have h1 : 0 < x ^ 2 - 9 := by nlinarith
  have h2 : 0 < x ^ 2 - 4 := by nlinarith
  have h3 : 0 < x ^ 2 - 1 := by nlinarith
  positivity

/-- (A4) at every real `x ≠ 0`, in index form. -/
theorem wg_real (hb : s.bndOK = true) (hw : ∀ i : Fin 24, s.wgRow i = true) {i : ℕ} (hi : i < 24)
    {x : ℝ} (hx : x ≠ 0) (a b : Fin s.k) :
    ∑ j ∈ range 24, x ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) * ev (1 / x) (f4 s.N j a b) =
      ev x Rl * x ^ s.e / x ^ 6 * ev x (f4 s.F i a b) := by
  have hrow := rng_spec (rng_spec (hw ⟨i, hi⟩) a.isLt) b.isLt
  rw [beq_iff_eq] at hrow
  have hbp := bnd_parts hb
  have hterm : ∀ j < 24, CB (X ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) * toP (rev 6 (f4 s.N j a b)))
      s.MN (7 + 4) := fun j hj =>
    (CB_X_pow_mul (CB_of_bndL hbp.2.2.2.1 (hbp.2.2.2.2.1 j hj a a.isLt b b.isLt).2.2) _).mono le_rfl
      (by have := cycTab_le (fin24 (mulInvIdx i j)); omega)
  have hP := CB_sum_range 24 hbp.2.2.2.1 hterm
  have hR : CB (toP Rl) 49 7 := CB_of_bndL (by norm_num) (by decide)
  have hQ := CB_mul hR (CB_X_pow_mul (CB_F hb hi a.isLt b.isLt) s.e)
  have hx' : 2 * ((24 : ℕ) * s.MN + 7 * (49 * s.MF)) < s.X := by
    have := hbp.2.2.2.2.2.2.2.2.1; simp only [SiteData.Bwg] at this; push_cast; exact this
  have key := ev_eq_of_kron hP hQ hx' (by
    simp only [eval_finset_sum, eval_mul, eval_pow, eval_X, eval_FX, eval_toP]
    rw [← lsum_eq']
    simpa [SiteData.FX, eval_toP] using hrow) x
  simp only [eval₂_finset_sum, eval₂_mul, eval₂_X_pow, ev_toP_eval₂] at key
  have hlen : ∀ j < 24, (f4 s.N j a b).length ≤ 6 + 1 := fun j hj => (hbp.2.2.2.2.1 j hj a a.isLt b b.isLt).2.1
  have e6 : x ^ 6 * ∑ j ∈ range 24, x ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) * ev (1 / x) (f4 s.N j a b) =
      ∑ j ∈ range 24, x ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) * ev x (rev 6 (f4 s.N j a b)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [← ev_rev hx 6 (hlen j (mem_range.mp hj))]; ring
  have h6 : x ^ 6 ≠ 0 := pow_ne_zero 6 hx
  calc _ = (x ^ 6 * ∑ j ∈ range 24, x ^ LayerDProto.cycTab (fin24 (mulInvIdx i j)) *
        ev (1 / x) (f4 s.N j a b)) / x ^ 6 := by field_simp
    _ = _ := by rw [e6, key]; field_simp

/-- (A3): `F(e)(d)` is positive definite for every real `d ≥ 4`. -/
theorem pd_real (hb : s.bndOK = true) (ht : s.transOK = true) (hp : s.pdOK = true) {x : ℝ}
    (hx : 4 ≤ x) : (s.FR x 0).PosDef := by
  simp only [SiteData.pdOK, Bool.and_eq_true] at hp
  obtain ⟨⟨-, hdom⟩, hW⟩ := hp
  set Wr : Matrix (Fin s.k) (Fin s.k) ℝ := Matrix.of fun a b => (s.wE a b : ℝ) with hWr
  have ev_plsum : ∀ ls : List (List ℤ), ev x (plsum ls) = (ls.map (ev x)).sum := by
    intro ls; induction ls with
    | nil => simp [plsum, ev_nil]
    | cons l ls ih => simp only [plsum, List.foldr_cons] at ih ⊢; rw [ev_padd, ih]; simp
  have hE : ∀ a b : Fin s.k, (Wr * s.FR x 0 * Wrᵀ) a b = ev x (s.El a b) := by
    intro a b
    simp only [SiteData.El, ev_plsum, List.map_map]
    rw [lsum_eq]
    simp only [Function.comp_def, ev_plsum, List.map_map]
    simp only [lsum_eq, Function.comp_def, ev_psmul]
    simp only [hWr, SiteData.FR, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← sum_fin_range s.k (fun t => ∑ u ∈ range s.k, ((s.wE a t * s.wE b u : ℤ) : ℝ) *
      ev x (f4 s.F 0 t u))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← sum_fin_range s.k (fun u => ((s.wE a t * s.wE b u : ℤ) : ℝ) * ev x (f4 s.F 0 t u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast; ring
  have hsymF : (s.FR x 0)ᵀ = s.FR x 0 := by
    rw [trans_real ht (by norm_num)]; congr 1
  have hsym : (Wr * s.FR x 0 * Wrᵀ)ᵀ = Wr * s.FR x 0 * Wrᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymF, Matrix.mul_assoc]
  have hdd : ∀ a, ∑ b, |(Wr * s.FR x 0 * Wrᵀ) a b| < 2 * (Wr * s.FR x 0 * Wrᵀ) a a := by
    intro a
    have hpos := domPos_spec (rng_spec hdom a.isLt) hx
    simp only [SiteData.domRow, ev_padd, ev_psmul, ev_plsum, List.map_map] at hpos
    rw [lsum_eq] at hpos
    simp only [hE]
    have hsplit : ∑ b : Fin s.k, |ev x (s.El a b)| = |ev x (s.El a a)| +
        ∑ b : Fin s.k, (if (b : ℕ) = a then 0 else |ev x (s.El a b)|) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, zero_add]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [if_neg]; intro h; exact (Finset.mem_erase.mp hb).1 (Fin.ext h)
    have hle : ∑ b : Fin s.k, (if (b : ℕ) = a then 0 else |ev x (s.El a b)|) ≤
        ∑ b ∈ range s.k, (Function.comp (ev x) fun b => if b = (a : ℕ) then [] else pabs (s.El a b)) b := by
      rw [← sum_fin_range s.k (fun b => (Function.comp (ev x) fun b => if b = (a : ℕ) then [] else
        pabs (s.El a b)) b)]
      refine Finset.sum_le_sum fun b _ => ?_
      simp only [Function.comp_apply]
      split_ifs
      · simp [ev_nil]
      · exact abs_ev_le x (by linarith) _
    have hdiag : 0 < ev x (s.El a a) := by
      have : 0 ≤ ∑ b ∈ range s.k, (Function.comp (ev x) fun b => if b = (a : ℕ) then [] else
          pabs (s.El a b)) b := le_trans (Finset.sum_nonneg fun b _ => by split_ifs <;> simp) hle
      push_cast at hpos; linarith
    rw [hsplit, abs_of_pos hdiag]
    push_cast at hpos
    linarith
  have hEpd := LayerDProto.posDef_of_diagDom _ hsym hdd
  -- congruence by the lower-triangular `W` with positive diagonal
  have hl : ∀ a b : Fin s.k, a < b → Wr a b = 0 := fun a b hab => by
    have := rng_spec (rng_spec hW a.isLt) b.isLt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp [hWr, this.1 hab]
  have hd : ∀ a, 0 < Wr a a := fun a => by
    have := rng_spec (rng_spec hW a.isLt) a.isLt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    revert this; simp [hWr]
  have htri : Wr.BlockTriangular OrderDual.toDual := fun i j hij => hl _ _ (by simpa using hij)
  have hdet : IsUnit Wr.det := by
    rw [det_of_lowerTriangular Wr htri, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne'
  have hdetT : IsUnit Wrᵀ.det := by rwa [det_transpose]
  have hA : s.FR x 0 = Wr⁻¹ * (Wr * s.FR x 0 * Wrᵀ) * (Wr⁻¹)ᴴ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_nonsing_inv]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hdetT, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
  rw [hA]
  refine hEpd.mul_mul_conjTranspose_same ?_
  exact vecMul_injective_iff_isUnit.mpr ((isUnit_nonsing_inv_iff).mpr ((isUnit_iff_isUnit_det _).mpr hdet))

end Sound

/-- A module from an adjugate-type identity: `F(e) A = δ 1` with `δ ≠ 0` and
`F(p) A F(q) = d^l δ F(s)` give `ModuleAt` with `H = F(e)⁻¹`. -/
theorem moduleAt_of_adjR {k : ℕ} {d : ℕ} {tab : P4 → P4 → P4 × ℕ} {F : P4 → Matrix (Fin k) (Fin k) ℝ}
    (A : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ) (hδ : δ ≠ 0) (hT : ∀ p, (F p)ᵀ = F p⁻¹)
    (hadj : F 1 * A = δ • 1)
    (hhom : ∀ p q, F p * A * F q = ((d : ℝ) ^ (tab p q).2 * δ) • F (tab p q).1)
    (hpd : (F 1).PosDef) : ModuleAt d tab F := by
  refine ⟨(F 1)⁻¹, hpd.inv.posSemidef, fun p q => ?_⟩
  have hdet : IsUnit (F 1).det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hA : A = δ • (F 1)⁻¹ := by
    calc A = (F 1)⁻¹ * (F 1 * A) := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = δ • (F 1)⁻¹ := by rw [hadj, Matrix.mul_smul, Matrix.mul_one]
  have h := hhom p⁻¹ q
  rw [hA, Matrix.mul_smul, Matrix.smul_mul, show ((d : ℝ) ^ (tab p⁻¹ q).2 * δ) =
    δ * (d : ℝ) ^ (tab p⁻¹ q).2 by ring, ← smul_smul] at h
  rw [hT p]
  exact (smul_right_injective _ hδ h).symm

theorem permTab_injective : Function.Injective permTab := fun a b h => by
  have := congrArg permIdx h
  rw [permIdx_permTab, permIdx_permTab] at this
  exact Fin.ext this

/-- `Fin 24 ≃ S₄` in the verifier's order. -/
noncomputable def permEquiv24 : Fin 24 ≃ P4 :=
  Equiv.ofBijective permTab ⟨permTab_injective, permTab_surj⟩

theorem invIdx_permIdx (p : P4) : invIdx (permIdx p) = permIdx p⁻¹ := by
  rw [invIdx, permTab_permIdx]

theorem mulInvIdx_eq (p : P4) (j : Fin 24) :
    permTab (fin24 (mulInvIdx (permIdx p) j)) = p⁻¹ * permTab j := by
  rw [mulInvIdx, permTab_permIdx, permTab_permIdx, fin24_val]

/-- **(A2)–(A4) ⇒ `SiteCert`.** -/
theorem siteCert_of_chk {s : SiteData} {S L : List (List ℕ)} (hb : s.bndOK = true)
    (ht : s.transOK = true) (ha : s.adjOK = true) (hh : ∀ i : Fin 24, s.homRow S L i = true)
    (hw : ∀ i : Fin 24, s.wgRow i = true) (hp : s.pdOK = true) :
    SiteCert (tabOf S L) (NP s.k s.N) := by
  intro d hd
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hδ : 0 < ev d s.δ := by
    simp only [SiteData.pdOK, Bool.and_eq_true] at hp
    exact domPos_spec hp.1.1 hd'
  refine ⟨fun p => s.FR d (permIdx p), ev d Rl * (d : ℝ) ^ s.e / (d : ℝ) ^ 6,
    by have := ev_Rl_pos hd'; positivity,
    moduleAt_of_adjR (s.AR d) (ev d s.δ) hδ.ne' (fun p => ?_) ?_ (fun p q => ?_) ?_, fun p => ?_⟩
  · rw [trans_real ht (permIdx_lt p), invIdx_permIdx]
  · simp only [permIdx_one]; exact adj_real hb ha _
  · obtain ⟨i, rfl⟩ := permTab_surj p
    obtain ⟨j, rfl⟩ := permTab_surj q
    simp only [tabOf_permTab, permIdx_permTab]
    exact hom_real hb hh i.isLt j.isLt _
  · simp only [permIdx_one]; exact pd_real hb ht hp hd'
  · ext a b
    have hw' := wg_real hb hw (permIdx_lt p) hd0 a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, SiteData.FR, Matrix.of_apply, NP,
      Polynomial.eval_map, ev_toP_eval₂]
    rw [← hw', ← permEquiv24.sum_comp, ← sum_fin_range 24]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [permEquiv24, Equiv.ofBijective_apply, gram, permIdx_permTab, fin24_val]
    rw [← mulInvIdx_eq p j, LayerDProto.cycCount_permTab]
    simp only [evalM, Matrix.map_apply, Matrix.of_apply, Polynomial.eval_map, one_div, permIdx_permTab]
    rfl

end LayerDT0

#print axioms LayerDT0.siteCert_of_chk
