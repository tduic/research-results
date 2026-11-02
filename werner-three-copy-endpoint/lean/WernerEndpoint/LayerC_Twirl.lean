import WernerEndpoint.LayerC_Sites
import WernerEndpoint.LayerB_Reduction

/-!
# Layer C (L7): the symmetrised twirled moments and the interface for layer D

Notation: one copy is `H = (κ → ι) × ρ` (sites and qubit); the four-replica space has
multi-indices `X : Fin 4 → H`. For a pair `a b : H → ℂ` the family moments are
`Ymom f31 a b = |aaab⟩⟨aaab|`, `Ymom f22 a b = |aabb⟩⟨aabb|`, `Ymom f13 a b = |bbba⟩⟨bbba|`
(the `moment`s of layer B and the `Y31`, `Y22`, `Y13` of L5).

**Construction.**
* `G = Perm κ × Bool` acts on vectors: `gact (π, ε) a (h, q) = cj ε (a (h ∘ π, q))`
  (site permutation, then complex conjugation when `ε`). `isLift_gact`: it maps lifts to lifts.
* `Ybar f a b = (1/|G|) ∑_{g ∈ G} Ymom f (g a) (g b)` (the average over site permutations and
  conjugation), and `twirl f a b` is its Hilbert–Schmidt projection onto `algT ∅ = span{P_t}`
  (`twirl_spec`). This is the Haar twirl over `U(d)^3 × U(2)` followed by the symmetrisation,
  done without Haar measure.

**Interface (what layer D uses).** For a lift `(a, b)` (`IsLift`: `Tr_H|a⟩⟨a| = I/2`,
`‖a‖ = ‖b‖ = 1`):
* (a) `twirl_rep`: `twirl f a b = ∑_t x_t P_t` for some real `x : Tup κ → ℝ` that is constant on
  the verifier's orbits: invariant under site permutations, componentwise inversion, and left and
  right multiplication by the bosonic group `bos f` of the family.
* (b) `twirl_objective`: `Tr[objective4 · twirl f31] = q(∑_r |a_r⟩⟨b_r|)`;
  `twirl_trace`: `Tr twirl f31 = 1`.
* (c) `twirl_row`: every row functional `∑_j c_j Tr[P_{w_j} Y_{f_j}]` that vanishes on all lifts
  vanishes on the twirled moments; the four row families of `verify_d5.py`:
  `twirl_contrast_row`, `twirl_row_31_22`, `twirl_row_22_13` (and the trace row above).
* (d) `twirl_ptrans_posSemidef`: `Γ_T(twirl f) ⪰ 0` for every cut `T` of the verifier;
  `twirl_coupled_T3_posSemidef`, `twirl_coupled_T23_posSemidef`: the two coupled 2×2 blocks
  `[[rearr σ₃₁ Ŷ31, rearr σ₂₂ Ŷ22], [(rearr σ₂₂ Ŷ22)ᴴ, rearr σ₁₃ Ŷ13]] ⪰ 0`.
* `qfun_nonneg_of_twirl`: if `0 ≤ Re Tr[objective4 · twirl f31 a b]` for every lift, then
  `q(C) ≥ 0` for every rank-`≤ 2` `C`.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

/-! ### Conjugation as a Boolean action -/

/-- `cj false z = z`, `cj true z = conj z`. -/
def cj : Bool → ℂ → ℂ
  | false, z => z
  | true, z => star z

theorem cj_mul (ε : Bool) (z w : ℂ) : cj ε (z * w) = cj ε z * cj ε w := by
  cases ε <;> simp [cj]

theorem cj_add (ε : Bool) (z w : ℂ) : cj ε (z + w) = cj ε z + cj ε w := by
  cases ε <;> simp [cj]

theorem cj_star (ε : Bool) (z : ℂ) : cj ε (star z) = star (cj ε z) := by
  cases ε <;> simp [cj]

theorem cj_cj (ε ε' : Bool) (z : ℂ) : cj ε (cj ε' z) = cj (xor ε ε') z := by
  cases ε <;> cases ε' <;> simp [cj]

theorem cj_ofReal (ε : Bool) (r : ℝ) : cj ε (r : ℂ) = r := by
  cases ε <;> simp [cj]

theorem cj_zero (ε : Bool) : cj ε 0 = 0 := by cases ε <;> simp [cj]

theorem cj_one (ε : Bool) : cj ε 1 = 1 := by cases ε <;> simp [cj]

theorem cj_sum {α : Type*} (ε : Bool) (s : Finset α) (f : α → ℂ) :
    cj ε (∑ x ∈ s, f x) = ∑ x ∈ s, cj ε (f x) := by
  cases ε <;> simp [cj, star_sum]

theorem cj_prod {α : Type*} (ε : Bool) (s : Finset α) (f : α → ℂ) :
    cj ε (∏ x ∈ s, f x) = ∏ x ∈ s, cj ε (f x) := by
  cases ε <;> simp [cj, star_prod]

theorem cj_ite (ε : Bool) (P : Prop) [Decidable P] :
    cj ε (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
  split_ifs <;> simp [cj_one, cj_zero]

section Twirl

variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ]

/-! ### The symmetry group `Perm κ × Bool` -/

/-- Site permutation of one copy: `(h, q) ↦ (h ∘ π, q)`. -/
def eH (π : Equiv.Perm κ) : (κ → ι) × ρ ≃ (κ → ι) × ρ where
  toFun x := (x.1 ∘ π, x.2)
  invFun x := (x.1 ∘ π.symm, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

/-- Site permutation of the four-replica multi-index. -/
def eX (π : Equiv.Perm κ) : (Fin 4 → (κ → ι) × ρ) ≃ (Fin 4 → (κ → ι) × ρ) :=
  Equiv.piCongrRight fun _ => eH π

theorem eX_apply (π : Equiv.Perm κ) (X : Fin 4 → (κ → ι) × ρ) (k : Fin 4) :
    eX π X k = ((X k).1 ∘ π, (X k).2) := rfl

/-- The action on vectors: `gact (π, ε) a (h, q) = cj ε (a (h ∘ π, q))`. -/
def gact (g : Equiv.Perm κ × Bool) (a : (κ → ι) × ρ → ℂ) : (κ → ι) × ρ → ℂ :=
  fun x => cj g.2 (a (eH g.1 x))

/-- The group law: `gact g₀ ∘ gact g = gact (g₀ ⋆ g)`. -/
def gmul (g₀ g : Equiv.Perm κ × Bool) : Equiv.Perm κ × Bool := (g₀.1 * g.1, xor g₀.2 g.2)

theorem gact_gact (g₀ g : Equiv.Perm κ × Bool) (a : (κ → ι) × ρ → ℂ) :
    gact g₀ (gact g a) = gact (gmul g₀ g) a := by
  funext x
  simp only [gact, gmul, cj_cj]
  rfl

/-- Left multiplication in `Perm κ × Bool` is a bijection. -/
def gmulEquiv (g₀ : Equiv.Perm κ × Bool) : Equiv.Perm κ × Bool ≃ Equiv.Perm κ × Bool where
  toFun g := gmul g₀ g
  invFun g := (g₀.1⁻¹ * g.1, xor g₀.2 g.2)
  left_inv g := by
    obtain ⟨π, ε⟩ := g
    simp [gmul, ← mul_assoc]
  right_inv g := by
    obtain ⟨π, ε⟩ := g
    simp [gmul, ← mul_assoc]

/-- Lifted pairs: `Tr_H |a⟩⟨a| = I/2` and `‖a‖ = ‖b‖ = 1` (the output of `lift_exists`). -/
def IsLift (a b : (κ → ι) × ρ → ℂ) : Prop :=
  (∀ s s', ∑ h, a (h, s) * star (a (h, s')) = if s = s' then (1 / 2 : ℂ) else 0) ∧
    vnormSq a = 1 ∧ vnormSq b = 1

/-- Site permutation of colourings of the sites. -/
def eS (π : Equiv.Perm κ) : (κ → ι) ≃ (κ → ι) where
  toFun h := h ∘ π
  invFun h := h ∘ π.symm
  left_inv h := by funext i; simp
  right_inv h := by funext i; simp

theorem nsqC_gact (g : Equiv.Perm κ × Bool) (a : (κ → ι) × ρ → ℂ) :
    nsqC (gact g a) = cj g.2 (nsqC a) := by
  simp only [nsqC, gact, cj_sum, cj_mul, cj_star]
  exact Equiv.sum_comp (eH (ι := ι) (ρ := ρ) g.1) (fun x => star (cj g.2 (a x)) * cj g.2 (a x))

theorem vnormSq_gact (g : Equiv.Perm κ × Bool) (a : (κ → ι) × ρ → ℂ) :
    vnormSq (gact g a) = vnormSq a := by
  have h := nsqC_gact g a
  rw [← ofReal_vnormSq, ← ofReal_vnormSq, cj_ofReal] at h
  exact_mod_cast h

/-- Site permutations and conjugation map lifts to lifts. -/
theorem isLift_gact (g : Equiv.Perm κ × Bool) {a b : (κ → ι) × ρ → ℂ} (h : IsLift a b) :
    IsLift (gact g a) (gact g b) := by
  obtain ⟨hm, ha, hb⟩ := h
  refine ⟨fun s s' => ?_, by rw [vnormSq_gact, ha], by rw [vnormSq_gact, hb]⟩
  have e : ∑ h, gact g a (h, s) * star (gact g a (h, s')) =
      cj g.2 (∑ h, a (h, s) * star (a (h, s'))) := by
    simp only [gact, cj_sum, cj_mul, cj_star]
    exact Equiv.sum_comp (eS (ι := ι) g.1) (fun h => cj g.2 (a (h, s)) * star (cj g.2 (a (h, s'))))
  rw [e, hm s s']
  split_ifs
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, cj_ofReal]
  · exact cj_zero _

/-! ### Families and the symmetrised moments -/

/-- The three moment families of `verify_d5.py`. -/
inductive Fam
  | f31
  | f22
  | f13
  deriving DecidableEq, Fintype

/-- Which replica slots carry `b` (letter pattern `AAAB`, `AABB`, `BBBA`). -/
def famPat : Fam → Fin 4 → Bool
  | .f31, k => decide (k = 3)
  | .f22, k => decide (2 ≤ k.val)
  | .f13, k => decide (k ≠ 3)

/-- The replica vectors of a family. -/
def famVec (f : Fam) (a b : (κ → ι) × ρ → ℂ) : Fin 4 → (κ → ι) × ρ → ℂ :=
  fun k => if famPat f k then b else a

theorem famVec_f31 (a b : (κ → ι) × ρ → ℂ) : famVec .f31 a b = ![a, a, a, b] := by
  funext k; fin_cases k <;> rfl

theorem famVec_f22 (a b : (κ → ι) × ρ → ℂ) : famVec .f22 a b = ![a, a, b, b] := by
  funext k; fin_cases k <;> rfl

theorem famVec_f13 (a b : (κ → ι) × ρ → ℂ) : famVec .f13 a b = ![b, b, b, a] := by
  funext k; fin_cases k <;> rfl

theorem famVec_gact (f : Fam) (g : Equiv.Perm κ × Bool) (a b : (κ → ι) × ρ → ℂ) :
    famVec f (gact g a) (gact g b) = fun k => gact g (famVec f a b k) := by
  funext k
  simp only [famVec]
  split_ifs <;> rfl

/-- The family moment `|⊗_k v_k⟩⟨⊗_k v_k|`. -/
def Ymom (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  moment (famVec f a b)

theorem Ymom_f31 (a b : (κ → ι) × ρ → ℂ) : Ymom .f31 a b = Y31 a b := by
  rw [Ymom, famVec_f31]; rfl

theorem Ymom_f22 (a b : (κ → ι) × ρ → ℂ) : Ymom .f22 a b = Y22 a b := by
  rw [Ymom, famVec_f22]; rfl

theorem Ymom_f13 (a b : (κ → ι) × ρ → ℂ) : Ymom .f13 a b = Y13 a b := by
  rw [Ymom, famVec_f13]; rfl

/-- The averaging weight `1/|G|` (a real number). -/
def avgW (κ : Type*) [Fintype κ] [DecidableEq κ] : ℂ :=
  (((Fintype.card (Equiv.Perm κ × Bool) : ℝ))⁻¹ : ℝ)

theorem avgW_nonneg : 0 ≤ avgW κ := by
  unfold avgW
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem star_avgW : star (avgW κ) = avgW κ := by
  unfold avgW; exact Complex.conj_ofReal _

theorem avgW_mul_card : avgW κ * (Fintype.card (Equiv.Perm κ × Bool) : ℂ) = 1 := by
  unfold avgW
  have h : (Fintype.card (Equiv.Perm κ × Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

/-- The average over site permutations and conjugation. -/
def Ybar (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  avgW κ • ∑ g : Equiv.Perm κ × Bool, Ymom f (gact g a) (gact g b)

theorem algT_empty_star {A : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ}
    (hA : A ∈ algT κ ι ρ ∅) : Aᴴ ∈ algT κ ι ρ ∅ := algT_star_mem hA

/-- The twirl: the projection of `Ybar` onto `span{P_t}`. -/
def twirl (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  Classical.choose (exists_isHSProj algT_empty_star (Ybar f a b))

theorem twirl_spec (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    IsHSProj (algT κ ι ρ ∅) (Ybar f a b) (twirl f a b) :=
  Classical.choose_spec (exists_isHSProj algT_empty_star (Ybar f a b))

theorem permOp_mem (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) :
    permOp ι ρ w wq ∈ algT κ ι ρ ∅ := by
  rw [← PT_empty (t := (w, wq))]
  exact PT_mem ∅ _

/-- Traces against `span{P_t}` see only the average. -/
theorem trace_mul_twirl {A : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ}
    (hA : A ∈ algT κ ι ρ ∅) (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    (A * twirl f a b).trace =
      avgW κ * ∑ g : Equiv.Perm κ × Bool, (A * Ymom f (gact g a) (gact g b)).trace := by
  rw [(twirl_spec f a b).trace_mul algT_star_mem hA, Ybar, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul]

theorem cj_sub (ε : Bool) (z w : ℂ) : cj ε (z - w) = cj ε z - cj ε w := by
  cases ε <;> simp [cj]

/-! ### The symmetry operators on the four-replica space -/

/-- The operator form of `g = (π, ε)`: `(OpG g M) X Y = cj ε (M (π X) (π Y))`. -/
def OpG (g : Equiv.Perm κ × Bool) (M : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  Matrix.of fun X Y => cj g.2 (M (eX g.1 X) (eX g.1 Y))

theorem prodVec_gact (g : Equiv.Perm κ × Bool) (v : Fin 4 → (κ → ι) × ρ → ℂ)
    (X : Fin 4 → (κ → ι) × ρ) :
    prodVec (fun k => gact g (v k)) X = cj g.2 (prodVec v (eX g.1 X)) := by
  simp only [prodVec, gact, cj_prod]
  rfl

theorem OpG_moment (g : Equiv.Perm κ × Bool) (v : Fin 4 → (κ → ι) × ρ → ℂ) :
    OpG g (moment v) = moment (fun k => gact g (v k)) := by
  ext X Y
  simp only [OpG, moment, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, prodVec_gact,
    cj_mul, cj_star]

theorem OpG_smul (g : Equiv.Perm κ × Bool) (c : ℂ) (M : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) :
    OpG g (c • M) = cj g.2 c • OpG g M := by
  ext X Y
  simp [OpG, cj_mul]

theorem OpG_add (g : Equiv.Perm κ × Bool) (M N : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) :
    OpG g (M + N) = OpG g M + OpG g N := by
  ext X Y
  simp [OpG, cj_add]

theorem OpG_sub (g : Equiv.Perm κ × Bool) (M N : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) :
    OpG g (M - N) = OpG g M - OpG g N := by
  ext X Y
  simp [OpG, cj_sub]

theorem OpG_sum {α : Type*} (g : Equiv.Perm κ × Bool) (s : Finset α)
    (M : α → Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ) :
    OpG g (∑ x ∈ s, M x) = ∑ x ∈ s, OpG g (M x) := by
  ext X Y
  simp [OpG, Matrix.sum_apply, cj_sum]

theorem cj_avgW (ε : Bool) : cj ε (avgW κ) = avgW κ := by
  unfold avgW; exact cj_ofReal _ _

/-- The average is invariant under the symmetry operators. -/
theorem OpG_Ybar (g₀ : Equiv.Perm κ × Bool) (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    OpG g₀ (Ybar f a b) = Ybar f a b := by
  rw [Ybar, OpG_smul, cj_avgW, OpG_sum]
  congr 1
  simp only [Ymom, OpG_moment, ← famVec_gact, gact_gact]
  exact Equiv.sum_comp (gmulEquiv g₀) (fun g => moment (famVec f (gact g a) (gact g b)))

theorem eX_permIdx (π : Equiv.Perm κ) (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (X : Fin 4 → (κ → ι) × ρ) :
    eX π (permIdx (fun i => w (π.symm i)) wq X) = permIdx w wq (eX π X) := by
  funext k
  refine Prod.ext (funext fun i => ?_) rfl
  show (X (w (π.symm (π i)) k)).1 (π i) = (X (w i k)).1 (π i)
  rw [Equiv.symm_apply_apply]

theorem OpG_permOp (g : Equiv.Perm κ × Bool) (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) :
    OpG g (permOp ι ρ w wq) = permOp ι ρ (fun i => w (g.1.symm i)) wq := by
  ext X Y
  simp only [OpG, permOp, Matrix.of_apply, cj_ite]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · apply (eX g.1).injective
    rw [h, eX_permIdx]
  · rw [h, eX_permIdx]

theorem hs_OpG (g : Equiv.Perm κ × Bool) (A B : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) :
    hs (OpG g A) (OpG g B) = cj g.2 (hs A B) := by
  rw [← hs_reindex (Equiv.prodCongr (eX g.1) (eX g.1)) A B, cj_sum]
  simp only [hs, OpG, Matrix.of_apply, cj_sum, cj_mul, cj_star, Equiv.prodCongr_apply,
    Prod.map_apply]

theorem OpG_OpG_inv (g : Equiv.Perm κ × Bool) (M : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) :
    OpG g (OpG (g.1⁻¹, g.2) M) = M := by
  ext X Y
  simp only [OpG, Matrix.of_apply, cj_cj, Bool.xor_self]
  have e : ∀ Z : Fin 4 → (κ → ι) × ρ, eX g.1⁻¹ (eX g.1 Z) = Z := by
    intro Z; funext k
    refine Prod.ext (funext fun i => ?_) rfl
    show (Z k).1 (g.1 (g.1⁻¹ i)) = (Z k).1 i
    rw [Equiv.Perm.apply_inv_self]
  rw [e, e]
  rfl

theorem OpG_mem (g : Equiv.Perm κ × Bool) {A : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ}
    (hA : A ∈ algT κ ι ρ ∅) : OpG g A ∈ algT κ ι ρ ∅ := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [PT_empty, OpG_permOp]
    exact permOp_mem _ _
  | zero =>
    have : OpG g (0 : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) = 0 := by
      ext X Y; simp [OpG, cj_zero]
    rw [this]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [OpG_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [OpG_smul]; exact Submodule.smul_mem _ _ hx

theorem isHSProj_OpG (g : Equiv.Perm κ × Bool) {Y Z : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ}
    (h : IsHSProj (algT κ ι ρ ∅) Y Z) : IsHSProj (algT κ ι ρ ∅) (OpG g Y) (OpG g Z) :=
  h.map (OpG g) (OpG_sub g) (fun A B hAB => by rw [hs_OpG, hAB, cj_zero])
    (fun A hA => OpG_mem g hA)
    (fun A' hA' => ⟨OpG (g.1⁻¹, g.2) A', OpG_mem _ hA', OpG_OpG_inv g A'⟩)

/-- The twirl is invariant under site permutations and conjugation. -/
theorem OpG_twirl (g : Equiv.Perm κ × Bool) (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    OpG g (twirl f a b) = twirl f a b := by
  have h := isHSProj_OpG g (twirl_spec f a b)
  rw [OpG_Ybar] at h
  exact h.unique (twirl_spec f a b)

/-! ### Positivity of the average and Hermiticity of the twirl -/

theorem moment_posSemidef (v : Fin 4 → (κ → ι) × ρ → ℂ) : (moment v).PosSemidef :=
  posSemidef_vecMulVec_self_star _

theorem posSemidef_avg {n : Type*} [Fintype n] {M : Equiv.Perm κ × Bool → Matrix n n ℂ}
    (h : ∀ g, (M g).PosSemidef) : (avgW κ • ∑ g, M g).PosSemidef := by
  refine Matrix.PosSemidef.smul ?_ avgW_nonneg
  classical
  have : ∀ s : Finset (Equiv.Perm κ × Bool), (∑ g ∈ s, M g).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Matrix.PosSemidef.zero
    | insert x s hx ih => rw [Finset.sum_insert hx]; exact (h x).add ih
  exact this _

theorem Ybar_posSemidef (f : Fam) (a b : (κ → ι) × ρ → ℂ) : (Ybar f a b).PosSemidef :=
  posSemidef_avg fun _ => moment_posSemidef _

theorem twirl_isHermitian (f : Fam) (a b : (κ → ι) × ρ → ℂ) : (twirl f a b).IsHermitian :=
  (twirl_spec f a b).isHermitian algT_star_mem (Ybar_posSemidef f a b).isHermitian

/-! ### Bosonic invariance -/

/-- The bosonic group of a family: replica permutations preserving the letter pattern
(`BOS` of `verify_d5.py`: `S{0,1,2}` for 31 and 13, `S{0,1} × S{2,3}` for 22). -/
def bos (f : Fam) : Set (Equiv.Perm (Fin 4)) := {g | ∀ k, famPat f (g k) = famPat f k}

theorem bos_inv {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) : g⁻¹ ∈ bos f := by
  intro k
  have := hg (g⁻¹ k)
  rw [Equiv.Perm.apply_inv_self] at this
  exact this.symm

theorem famVec_bos {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (a b : (κ → ι) × ρ → ℂ)
    (k : Fin 4) : famVec f a b (g k) = famVec f a b k := by
  simp only [famVec, hg k]

theorem permIdx_diag (g : Equiv.Perm (Fin 4)) (X : Fin 4 → (κ → ι) × ρ) :
    permIdx (fun _ : κ => g) g X = fun k => X (g k) := rfl

/-- **Bosonic invariance of a word value.** If `P_g` permutes equal slots, `P_g |⊗v⟩ = |⊗v⟩`. -/
theorem permOp_mulVec_prodVec {g : Equiv.Perm (Fin 4)} {v : Fin 4 → (κ → ι) × ρ → ℂ}
    (hv : ∀ k, v (g k) = v k) :
    permOp ι ρ (fun _ : κ => g) g *ᵥ prodVec v = prodVec v := by
  rw [permOp_mulVec]
  funext X
  simp only [permIdx_diag, prodVec]
  conv_lhs => arg 2; ext k; rw [← hv k]
  exact Equiv.prod_comp g (fun k => v k (X k))

/-- `wordVal` is unchanged when `P_g` permutes equal slots: `P_g · moment v = moment v`. -/
theorem permOp_mul_moment {g : Equiv.Perm (Fin 4)} {v : Fin 4 → (κ → ι) × ρ → ℂ}
    (hv : ∀ k, v (g k) = v k) : permOp ι ρ (fun _ : κ => g) g * moment v = moment v := by
  rw [moment, Matrix.mul_vecMulVec, permOp_mulVec_prodVec hv]

theorem moment_mul_permOp {g : Equiv.Perm (Fin 4)} {v : Fin 4 → (κ → ι) × ρ → ℂ}
    (hv : ∀ k, v (g k) = v k) : moment v * permOp ι ρ (fun _ : κ => g) g = moment v := by
  have hv' : ∀ k, v (g⁻¹ k) = v k := fun k => by
    have := hv (g⁻¹ k); rw [Equiv.Perm.apply_inv_self] at this; exact this.symm
  have hH : (moment v)ᴴ = moment v := (moment_posSemidef v).isHermitian.eq
  have e := permOp_mul_moment (ι := ι) (ρ := ρ) (κ := κ) hv'
  rw [← permOp_conjTranspose (w := fun _ : κ => g) (wq := g)] at e
  have e2 := congrArg conjTranspose e
  rw [conjTranspose_mul, conjTranspose_conjTranspose, hH] at e2
  exact e2

/-- **Bosonic invariance of words** (left): if `P_g` permutes equal slots of `v`,
`wordVal (g w) (g wq) v = wordVal w wq v`. -/
theorem wordVal_bos_left {g : Equiv.Perm (Fin 4)} {v : Fin 4 → (κ → ι) × ρ → ℂ}
    (hv : ∀ k, v (g k) = v k) (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) :
    wordVal (fun i => g * w i) (g * wq) v = wordVal w wq v := by
  rw [← trace_permOp_moment, ← trace_permOp_moment, ← permOp_mul (ι := ι) (ρ := ρ)
    (fun _ : κ => g) w g wq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    moment_mul_permOp hv]

/-- **Bosonic invariance of words** (right). -/
theorem wordVal_bos_right {g : Equiv.Perm (Fin 4)} {v : Fin 4 → (κ → ι) × ρ → ℂ}
    (hv : ∀ k, v (g k) = v k) (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) :
    wordVal (fun i => w i * g) (wq * g) v = wordVal w wq v := by
  rw [← trace_permOp_moment, ← trace_permOp_moment, ← permOp_mul (ι := ι) (ρ := ρ)
    w (fun _ : κ => g) wq g, Matrix.mul_assoc, permOp_mul_moment hv]

theorem Ybar_bos_left {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (a b : (κ → ι) × ρ → ℂ) :
    permOp ι ρ (fun _ : κ => g) g * Ybar f a b = Ybar f a b := by
  rw [Ybar, Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun h _ => permOp_mul_moment (famVec_bos hg _ _)

theorem Ybar_bos_right {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (a b : (κ → ι) × ρ → ℂ) :
    Ybar f a b * permOp ι ρ (fun _ : κ => g) g = Ybar f a b := by
  rw [Ybar, Matrix.smul_mul, Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun h _ => moment_mul_permOp (famVec_bos hg _ _)

/-- **Bosonic invariance of the twirl**: `P_g Ŷ = Ŷ P_g = Ŷ` for `g` in the bosonic group. -/
theorem twirl_bos_left {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (a b : (κ → ι) × ρ → ℂ) :
    permOp ι ρ (fun _ : κ => g) g * twirl f a b = twirl f a b := by
  have h := (twirl_spec f a b).mul_left isStarAlg_algT_empty
    (permOp_mem (fun _ : κ => g) g)
  rw [Ybar_bos_left hg] at h
  exact h.unique (twirl_spec f a b)

theorem twirl_bos_right {f : Fam} {g : Equiv.Perm (Fin 4)} (hg : g ∈ bos f) (a b : (κ → ι) × ρ → ℂ) :
    twirl f a b * permOp ι ρ (fun _ : κ => g) g = twirl f a b := by
  have h := (twirl_spec f a b).mul_right isStarAlg_algT_empty
    (permOp_mem (fun _ : κ => g) g)
  rw [Ybar_bos_right hg] at h
  exact h.unique (twirl_spec f a b)

end Twirl

/-! ### Averaging a representation over a finite group of index symmetries -/

section Average

variable {Tp V : Type*} [Fintype Tp] [DecidableEq Tp] [AddCommGroup V] [Module ℂ V]

/-- If every generator `ψ ∈ S` and complex conjugation preserve the set of coefficient vectors
representing `M`, there is a **real** representing vector invariant under every `ψ ∈ S`
(average over the finite group generated by `S`, then take real parts). -/
theorem exists_real_invariant_rep (P : Tp → V) (M : V) (S : Set (Equiv.Perm Tp))
    (h0 : ∃ c : Tp → ℂ, ∑ t, c t • P t = M)
    (hS : ∀ ψ ∈ S, ∀ c : Tp → ℂ, ∑ t, c t • P t = M → ∑ t, c (ψ t) • P t = M)
    (hconj : ∀ c : Tp → ℂ, ∑ t, c t • P t = M → ∑ t, star (c t) • P t = M) :
    ∃ x : Tp → ℝ, ∑ t, (x t : ℂ) • P t = M ∧ ∀ ψ ∈ S, ∀ t, x (ψ t) = x t := by
  classical
  let Rep : (Tp → ℂ) → Prop := fun c => ∑ t, c t • P t = M
  let K := Subgroup.closure S
  have hpow : ∀ k : Equiv.Perm Tp, (∀ c, Rep c → Rep (fun t => c (k t))) →
      ∀ n : ℕ, ∀ c, Rep c → Rep (fun t => c ((k ^ n) t)) := by
    intro k hk n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      have := hk _ (ih c hc)
      simpa [pow_succ, Equiv.Perm.mul_apply] using this
  have hK : ∀ k ∈ K, ∀ c, Rep c → Rep (fun t => c (k t)) := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => intro c hc; simpa using hc
    | mul x y _ _ hx hy =>
      intro c hc
      have := hy _ (hx c hc)
      simpa [Equiv.Perm.mul_apply] using this
    | inv x _ hx =>
      have hn := orderOf_pos x
      have hinv : x ^ (orderOf x - 1) = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      intro c hc
      have := hpow x hx (orderOf x - 1) c hc
      rw [hinv] at this
      exact this
  have hre : ∀ c, Rep c → Rep (fun t => ((c t).re : ℂ)) := by
    intro c hc
    have h2 : ∑ t, star (c t) • P t = M := hconj c hc
    have e : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (2 : ℂ)⁻¹ * z + (2 : ℂ)⁻¹ * star z := fun z => by
      rw [Complex.re_eq_add_conj, starRingEnd_apply]; ring
    show ∑ t, ((c t).re : ℂ) • P t = M
    simp only [e, add_smul, Finset.sum_add_distrib]
    simp only [← smul_smul, ← Finset.smul_sum]
    rw [hc, h2, ← add_smul]
    norm_num
  obtain ⟨c₀, hc₀⟩ := h0
  haveI : Fintype K := Fintype.ofFinite K
  let n : ℝ := Fintype.card K
  have hn : (n : ℝ) ≠ 0 := by
    simp only [n]; exact_mod_cast Fintype.card_ne_zero
  let x : Tp → ℝ := fun t => n⁻¹ * ∑ k : K, (c₀ ((k : Equiv.Perm Tp) t)).re
  refine ⟨x, ?_, ?_⟩
  · have hk : ∀ k : K, ∑ t, ((c₀ ((k : Equiv.Perm Tp) t)).re : ℂ) • P t = M :=
      fun k => hre _ (hK k k.2 c₀ hc₀)
    calc ∑ t, (x t : ℂ) • P t
        = ∑ t, ((n⁻¹ : ℝ) : ℂ) • ∑ k : K, ((c₀ ((k : Equiv.Perm Tp) t)).re : ℂ) • P t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [x, Complex.ofReal_mul, Complex.ofReal_sum]
          rw [← smul_smul, Finset.sum_smul, Finset.smul_sum]
      _ = ((n⁻¹ : ℝ) : ℂ) • ∑ k : K, ∑ t, ((c₀ ((k : Equiv.Perm Tp) t)).re : ℂ) • P t := by
          rw [← Finset.smul_sum, Finset.sum_comm]
      _ = ((n⁻¹ : ℝ) : ℂ) • ∑ _k : K, M := by simp only [hk]
      _ = M := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
          have : ((n⁻¹ : ℝ) : ℂ) * (Fintype.card K : ℂ) = 1 := by
            rw [show (Fintype.card K : ℂ) = ((n : ℝ) : ℂ) by simp [n]]
            rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
          rw [this, one_smul]
  · intro ψ hψ t
    have hψK : ψ ∈ K := Subgroup.subset_closure hψ
    simp only [x]
    congr 1
    exact Equiv.sum_comp (Equiv.mulRight (⟨ψ, hψK⟩ : K))
      (fun k : K => (c₀ ((k : Equiv.Perm Tp) t)).re)

end Average

section Rep

variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ]

/-! ### The orbit generators of `verify_d5.py` on diagram tuples -/

/-- Site permutation of a diagram tuple: `t ↦ (t ∘ π, tq)` (the verifier's swaps of `t0, t1, t2`). -/
def sitePermT (π : Equiv.Perm κ) : Equiv.Perm (Tup κ) where
  toFun t := (fun i => t.1 (π i), t.2)
  invFun t := (fun i => t.1 (π.symm i), t.2)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

/-- Componentwise inversion (the verifier's `INVI`, transposition). -/
def invT : Equiv.Perm (Tup κ) where
  toFun t := (fun i => (t.1 i)⁻¹, t.2⁻¹)
  invFun t := (fun i => (t.1 i)⁻¹, t.2⁻¹)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

/-- Left multiplication by `g` in every component (`MULI[g][x]`). -/
def lmulT (g : Equiv.Perm (Fin 4)) : Equiv.Perm (Tup κ) where
  toFun t := (fun i => g * t.1 i, g * t.2)
  invFun t := (fun i => g⁻¹ * t.1 i, g⁻¹ * t.2)
  left_inv t := by ext <;> simp [← mul_assoc]
  right_inv t := by ext <;> simp [← mul_assoc]

/-- Right multiplication by `g` in every component (`MULI[x][g]`). -/
def rmulT (g : Equiv.Perm (Fin 4)) : Equiv.Perm (Tup κ) where
  toFun t := (fun i => t.1 i * g, t.2 * g)
  invFun t := (fun i => t.1 i * g⁻¹, t.2 * g⁻¹)
  left_inv t := by ext <;> simp [mul_assoc]
  right_inv t := by ext <;> simp [mul_assoc]

/-- The orbit generators of a family. -/
def orbitGens (κ : Type*) [Fintype κ] [DecidableEq κ] (f : Fam) : Set (Equiv.Perm (Tup κ)) :=
  Set.range sitePermT ∪ {invT} ∪ lmulT '' bos f ∪ rmulT '' bos f

theorem rep_reindex {M : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ}
    (φ : Equiv.Perm (Tup κ)) (c : Tup κ → ℂ)
    (h : ∑ t, c t • permOp ι ρ (φ t).1 (φ t).2 = M) :
    ∑ t, c (φ.symm t) • permOp ι ρ t.1 t.2 = M := by
  rw [← h, ← Equiv.sum_comp φ (fun t => c (φ.symm t) • permOp ι ρ t.1 t.2)]
  simp only [Equiv.symm_apply_apply]

theorem OpG_rep (g : Equiv.Perm κ × Bool) (c : Tup κ → ℂ) :
    OpG g (∑ t, c t • permOp ι ρ t.1 t.2) =
      ∑ t, cj g.2 (c t) • permOp ι ρ (fun i => t.1 (g.1.symm i)) t.2 := by
  rw [OpG_sum]
  simp only [OpG_smul, OpG_permOp]

/-- **(a) The orbit representation.** The twirl is a real combination of the permutation operators
whose coefficients are constant on the verifier's orbits. -/
theorem twirl_rep (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    ∃ x : Tup κ → ℝ, twirl f a b = ∑ t, (x t : ℂ) • permOp ι ρ t.1 t.2 ∧
      (∀ π t, x (sitePermT π t) = x t) ∧ (∀ t, x (invT t) = x t) ∧
      (∀ g ∈ bos f, ∀ t, x (lmulT g t) = x t) ∧ (∀ g ∈ bos f, ∀ t, x (rmulT g t) = x t) := by
  let P : Tup κ → Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ := fun t => permOp ι ρ t.1 t.2
  have hconj : ∀ c : Tup κ → ℂ, ∑ t, c t • P t = twirl f a b → ∑ t, star (c t) • P t = twirl f a b := by
    intro c hc
    have h := OpG_rep (ι := ι) (ρ := ρ) ((1 : Equiv.Perm κ), true) c
    rw [hc, OpG_twirl] at h
    exact h.symm
  have h0 : ∃ c : Tup κ → ℂ, ∑ t, c t • P t = twirl f a b := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (twirl_spec f a b).1
    exact ⟨c, by simpa only [PT_empty] using hc⟩
  have hS : ∀ ψ ∈ orbitGens κ f, ∀ c : Tup κ → ℂ, ∑ t, c t • P t = twirl f a b →
      ∑ t, c (ψ t) • P t = twirl f a b := by
    intro ψ hψ c hc
    rcases hψ with ((⟨π, rfl⟩ | hinv) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩
    · -- site permutation
      have h := OpG_rep (ι := ι) (ρ := ρ) (π, false) c
      rw [hc, OpG_twirl] at h
      have := rep_reindex (ι := ι) (ρ := ρ) (sitePermT π).symm c h.symm
      simpa only [Equiv.symm_symm] using this
    · -- inversion: Hermiticity, then conjugation
      rw [Set.mem_singleton_iff] at hinv
      subst hinv
      have hH : ∑ t, star (c t) • P (invT t) = twirl f a b := by
        have h := congrArg conjTranspose hc
        rw [(twirl_isHermitian f a b).eq, conjTranspose_sum] at h
        simpa only [conjTranspose_smul, P, permOp_conjTranspose] using h
      have h2 := rep_reindex (ι := ι) (ρ := ρ) invT (fun t => star (c t)) hH
      have h3 := hconj _ h2
      simpa only [star_star] using h3
    · -- left multiplication
      have h1 : ∑ t, c t • permOp ι ρ ((lmulT g⁻¹) t).1 ((lmulT g⁻¹) t).2 = twirl f a b := by
        rw [← twirl_bos_left (bos_inv hg) a b, ← hc, Matrix.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.mul_smul, permOp_mul]
        rfl
      have e : ∀ t : Tup κ, (lmulT g⁻¹).symm t = lmulT g t := fun t => by ext <;> simp [lmulT]
      simpa only [e] using rep_reindex (ι := ι) (ρ := ρ) (lmulT g⁻¹) c h1
    · -- right multiplication
      have h1 : ∑ t, c t • permOp ι ρ ((rmulT g⁻¹) t).1 ((rmulT g⁻¹) t).2 = twirl f a b := by
        rw [← twirl_bos_right (bos_inv hg) a b, ← hc, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.smul_mul, permOp_mul]
        rfl
      have e : ∀ t : Tup κ, (rmulT g⁻¹).symm t = rmulT g t := fun t => by ext <;> simp [rmulT]
      simpa only [e] using rep_reindex (ι := ι) (ρ := ρ) (rmulT g⁻¹) c h1
  obtain ⟨x, hx, hinv⟩ := exists_real_invariant_rep P (twirl f a b) (orbitGens κ f) h0 hS hconj
  refine ⟨x, hx.symm, fun π t => hinv _ (Or.inl (Or.inl (Or.inl ⟨π, rfl⟩))) t,
    fun t => hinv _ (Or.inl (Or.inl (Or.inr rfl))) t,
    fun g hg t => hinv _ (Or.inl (Or.inr ⟨g, hg, rfl⟩)) t,
    fun g hg t => hinv _ (Or.inr ⟨g, hg, rfl⟩) t⟩

/-! ### (d) Positivity of the word blocks and of the coupled blocks -/

theorem ptrans_Ybar (T : Finset (Fin 4)) (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (Ybar f a b) =
      avgW κ • ∑ g : Equiv.Perm κ × Bool,
        ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (Ymom f (gact g a) (gact g b)) := by
  show ptransL κ ι ρ T (avgW κ • ∑ g, _) = _
  rw [map_smul, map_sum]
  rfl

theorem rearr_Ybar (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    rearr σ (Ybar f a b) = avgW κ • ∑ g : Equiv.Perm κ × Bool, rearr σ (Ymom f (gact g a) (gact g b)) := by
  show rearrL κ ι ρ σ (avgW κ • ∑ g, _) = _
  rw [map_smul, map_sum]
  rfl

/-- **(d) Word blocks.** `Γ_T(Ŷ_f) ⪰ 0` for every cut `T` of the verifier. -/
theorem twirl_ptrans_posSemidef [Nonempty ι] [Nonempty ρ] {T : Finset (Fin 4)} (hT : IsCut T)
    (f : Fam) (a b : (κ → ι) × ρ → ℂ) :
    (ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (twirl f a b)).PosSemidef := by
  refine (isHSProj_ptrans T (twirl_spec f a b)).posSemidef (isStarAlg_algT hT) ?_
  rw [ptrans_Ybar]
  refine posSemidef_avg fun g => ?_
  rw [Ymom, moment, ← prodOp_vecMulVec]
  exact ptrans_prodOp_rankOne_posSemidef T _

theorem fromBlocks_avg {n : Type*}
    (A B C D : Equiv.Perm κ × Bool → Matrix n n ℂ) :
    fromBlocks (avgW κ • ∑ g, A g) (avgW κ • ∑ g, B g) (avgW κ • ∑ g, C g) (avgW κ • ∑ g, D g) =
      avgW κ • ∑ g, fromBlocks (A g) (B g) (C g) (D g) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

theorem conjTranspose_avg {n : Type*} (B : Equiv.Perm κ × Bool → Matrix n n ℂ) :
    (avgW κ • ∑ g, B g)ᴴ = avgW κ • ∑ g, (B g)ᴴ := by
  rw [conjTranspose_smul, star_avgW, conjTranspose_sum]

/-- Generic coupled-block positivity from three rearrangements with the L5 and L6 properties. -/
theorem twirl_coupled_posSemidef [Nonempty ι] [Nonempty ρ] {T : Finset (Fin 4)} (hT : IsCut T)
    (σ₁ σ₂ σ₃ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (m₁ m₂ m₃ : Fin 24 → Fin 24)
    (h₁ι : ∀ i : Fin 24, rearr σ₁ (sP ι (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ι) T (sP ι (permTab (m₁ i))))
    (h₁ρ : ∀ i : Fin 24, rearr σ₁ (sP ρ (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ρ) T (sP ρ (permTab (m₁ i))))
    (h₂ι : ∀ i : Fin 24, rearr σ₂ (sP ι (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ι) T (sP ι (permTab (m₂ i))))
    (h₂ρ : ∀ i : Fin 24, rearr σ₂ (sP ρ (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ρ) T (sP ρ (permTab (m₂ i))))
    (h₃ι : ∀ i : Fin 24, rearr σ₃ (sP ι (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ι) T (sP ι (permTab (m₃ i))))
    (h₃ρ : ∀ i : Fin 24, rearr σ₃ (sP ρ (permTab i)) =
      ptrans (ι := fun _ : Fin 4 => ρ) T (sP ρ (permTab (m₃ i))))
    (s₁ : ∀ j, ∃ i, m₁ i = j) (s₂ : ∀ j, ∃ i, m₂ i = j) (s₃ : ∀ j, ∃ i, m₃ i = j)
    (hblock : ∀ a b : (κ → ι) × ρ → ℂ,
      (fromBlocks (rearr σ₁ (Ymom .f31 a b)) (rearr σ₂ (Ymom .f22 a b))
        (rearr σ₂ (Ymom .f22 a b))ᴴ (rearr σ₃ (Ymom .f13 a b))).PosSemidef)
    (a b : (κ → ι) × ρ → ℂ) :
    (fromBlocks (rearr σ₁ (twirl .f31 a b)) (rearr σ₂ (twirl .f22 a b))
      (rearr σ₂ (twirl .f22 a b))ᴴ (rearr σ₃ (twirl .f13 a b))).PosSemidef := by
  have p₁ := isHSProj_rearr σ₁ T (tupMap m₁)
    (rearr_permOp_of_sites (κ := κ) σ₁ T m₁ h₁ι h₁ρ) (tupMap_surj s₁) (twirl_spec .f31 a b)
  have p₂ := isHSProj_rearr σ₂ T (tupMap m₂)
    (rearr_permOp_of_sites (κ := κ) σ₂ T m₂ h₂ι h₂ρ) (tupMap_surj s₂) (twirl_spec .f22 a b)
  have p₃ := isHSProj_rearr σ₃ T (tupMap m₃)
    (rearr_permOp_of_sites (κ := κ) σ₃ T m₃ h₃ι h₃ρ) (tupMap_surj s₃) (twirl_spec .f13 a b)
  refine posSemidef_fromBlocks_of_isHSProj (isStarAlg_algT hT) p₁ p₂
    (p₂.conjTranspose algT_star_mem) p₃ ?_
  rw [rearr_Ybar, rearr_Ybar, rearr_Ybar, conjTranspose_avg, fromBlocks_avg]
  exact posSemidef_avg fun g => hblock _ _

theorem isCut_T3 : IsCut ({3} : Finset (Fin 4)) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem isCut_T23 : IsCut ({2, 3} : Finset (Fin 4)) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- **(d) Coupled block, `T = {3}`** (`MAPS["c3"]`): 2-positivity of the projection. -/
theorem twirl_coupled_T3_posSemidef [Nonempty ι] [Nonempty ρ] (a b : (κ → ι) × ρ → ℂ) :
    (fromBlocks (rearr sigmaT3_31 (twirl .f31 a b)) (rearr sigmaT3_22 (twirl .f22 a b))
      (rearr sigmaT3_22 (twirl .f22 a b))ᴴ (rearr sigmaT3_13 (twirl .f13 a b))).PosSemidef :=
  twirl_coupled_posSemidef isCut_T3 _ _ _ mT3_31 mT3_22 mT3_13
    (rearr_sP_T3_31 ι) (rearr_sP_T3_31 ρ) (rearr_sP_T3_22 ι) (rearr_sP_T3_22 ρ)
    (rearr_sP_T3_13 ι) (rearr_sP_T3_13 ρ) mT3_31_surj mT3_22_surj mT3_13_surj
    (fun a b => by
      rw [Ymom_f31, Ymom_f22, Ymom_f13]
      exact coupled_block_T3_posSemidef a b) a b

/-- **(d) Coupled block, `T = {2,3}`** (`MAPS["c23"]`). -/
theorem twirl_coupled_T23_posSemidef [Nonempty ι] [Nonempty ρ] (a b : (κ → ι) × ρ → ℂ) :
    (fromBlocks (rearr sigmaT23_31 (twirl .f31 a b)) (rearr sigmaT23_22 (twirl .f22 a b))
      (rearr sigmaT23_22 (twirl .f22 a b))ᴴ (rearr sigmaT23_13 (twirl .f13 a b))).PosSemidef :=
  twirl_coupled_posSemidef isCut_T23 _ _ _ mT23_31 mT23_22 mT23_13
    (rearr_sP_T23_31 ι) (rearr_sP_T23_31 ρ) (rearr_sP_T23_22 ι) (rearr_sP_T23_22 ρ)
    (rearr_sP_T23_13 ι) (rearr_sP_T23_13 ρ) mT23_31_surj mT23_22_surj mT23_13_surj
    (fun a b => by
      rw [Ymom_f31, Ymom_f22, Ymom_f13]
      exact coupled_block_T23_posSemidef a b) a b

/-! ### (c) Rows -/

theorem trace_permOp_twirl (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) (f : Fam)
    (a b : (κ → ι) × ρ → ℂ) :
    (permOp ι ρ w wq * twirl f a b).trace =
      avgW κ * ∑ g : Equiv.Perm κ × Bool, wordVal w wq (famVec f (gact g a) (gact g b)) := by
  rw [trace_mul_twirl (permOp_mem w wq)]
  simp only [Ymom, trace_permOp_moment]

/-- **(c) Rows.** A row functional `∑_j c_j Tr[P_{w_j} Y_{f_j}]` that vanishes on every lift
vanishes on the twirled moments of every lift. -/
theorem twirl_row {J : Type*} [Fintype J] (fam : J → Fam) (coef : J → ℂ)
    (w : J → κ → Equiv.Perm (Fin 4)) (wq : J → Equiv.Perm (Fin 4))
    (hrow : ∀ a b : (κ → ι) × ρ → ℂ, IsLift a b →
      ∑ j, coef j * wordVal (w j) (wq j) (famVec (fam j) a b) = 0)
    {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) :
    ∑ j, coef j * (permOp ι ρ (w j) (wq j) * twirl (fam j) a b).trace = 0 := by
  simp only [trace_permOp_twirl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g _ => ?_
  have h := hrow _ _ (isLift_gact g hab)
  calc ∑ j, coef j * (avgW κ * wordVal (w j) (wq j) (famVec (fam j) (gact g a) (gact g b)))
      = avgW κ * ∑ j, coef j * wordVal (w j) (wq j) (famVec (fam j) (gact g a) (gact g b)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [h, mul_zero]

theorem nsqC_of_vnormSq {a : (κ → ι) × ρ → ℂ} (h : vnormSq a = 1) : nsqC a = 1 := by
  rw [← ofReal_vnormSq, h, Complex.ofReal_one]

/-- **(c) Trace row.** `Tr Ŷ31 = 1`. -/
theorem twirl_trace {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) : (twirl .f31 a b).trace = 1 := by
  have h := trace_mul_twirl (A := 1) isStarAlg_algT_empty.one_mem .f31 a b
  rw [Matrix.one_mul] at h
  rw [h]
  have : ∀ g : Equiv.Perm κ × Bool, (1 * Ymom .f31 (gact g a) (gact g b)).trace = 1 := by
    intro g
    obtain ⟨-, ha, hb⟩ := isLift_gact g hab
    rw [Matrix.one_mul, Ymom, famVec_f31]
    exact trace_Y31 _ _ (nsqC_of_vnormSq ha) (nsqC_of_vnormSq hb)
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact avgW_mul_card

/-- **(c) Contrast rows** (slot `r` carries `a`, all site permutations fix `r`, `|ρ| = 2`). -/
theorem twirl_contrast_row (f : Fam) (r : Fin 4) (hr : famPat f r = false)
    (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) (hw : ∀ i, w i r = r)
    (hρ : Fintype.card ρ = 2) {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) :
    2 * (permOp ι ρ w wq * twirl f a b).trace =
      (if wq r = r then 2 else 1) * (permOp ι ρ w (removeSlot wq r) * twirl f a b).trace := by
  have h := twirl_row (J := Fin 2) (fun _ => f) ![2, -(if wq r = r then 2 else 1)] (fun _ => w)
    ![wq, removeSlot wq r] (fun a b hab => ?_) hab
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hv : famVec f a b r = a := by simp [famVec, hr]
    have := contrast_row w wq r hw (famVec f a b) (by rw [hv]; exact hab.1) hρ
    linear_combination this

/-- **(c) 31–22 rows.** -/
theorem twirl_row_31_22 (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (hw : ∀ i, w i 2 = 2) (hq : wq 2 = 2) {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) :
    (permOp ι ρ w wq * twirl .f31 a b).trace = (permOp ι ρ w wq * twirl .f22 a b).trace := by
  have h := twirl_row (J := Fin 2) ![.f31, .f22] ![1, -1] (fun _ => w) (fun _ => wq)
    (fun a b hab => ?_) hab
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, famVec_f31,
      famVec_f22]
    have ha := nsqC_of_vnormSq hab.2.1
    have hb := nsqC_of_vnormSq hab.2.2
    have := row_31_22 a b (ha.trans hb.symm) (by rw [ha]; exact one_ne_zero) w wq hw hq
    linear_combination this

/-- **(c) 22–13 rows** (`π = PI_ABB`). -/
theorem twirl_row_22_13 (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (hw : ∀ i, w i 1 = 1) (hq : wq 1 = 1) {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) :
    (permOp ι ρ w wq * twirl .f22 a b).trace =
      (permOp ι ρ (fun i => piABB * w i * piABB⁻¹) (piABB * wq * piABB⁻¹) * twirl .f13 a b).trace := by
  have h := twirl_row (J := Fin 2) ![.f22, .f13] ![1, -1]
    ![w, fun i => piABB * w i * piABB⁻¹] ![wq, piABB * wq * piABB⁻¹] (fun a b hab => ?_) hab
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, famVec_f22,
      famVec_f13]
    have ha := nsqC_of_vnormSq hab.2.1
    have hb := nsqC_of_vnormSq hab.2.2
    have := row_22_13 a b (ha.trans hb.symm) (by rw [ha]; exact one_ne_zero) w wq hw hq
    linear_combination this

/-! ### (b) The objective -/

theorem wordVal_gact (g : Equiv.Perm κ × Bool) (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (v : Fin 4 → (κ → ι) × ρ → ℂ) :
    wordVal w wq (fun k => gact g (v k)) = cj g.2 (wordVal (fun i => w (g.1 i)) wq v) := by
  have e : ∀ X : Fin 4 → (κ → ι) × ρ,
      eX g.1 (permIdx w wq X) = permIdx (fun i => w (g.1 i)) wq (eX g.1 X) := by
    intro X
    have := eX_permIdx g.1 (fun i => w (g.1 i)) wq X
    simpa only [Equiv.apply_symm_apply] using this
  simp only [wordVal, prodVec_gact, e, cj_sum, cj_mul, cj_star]
  exact Equiv.sum_comp (eX g.1)
    (fun Y => star (cj g.2 (prodVec v Y)) * cj g.2 (prodVec v (permIdx (fun i => w (g.1 i)) wq Y)))

theorem trace_objective4_moment (v : Fin 4 → (κ → ι) × ρ → ℂ) :
    (objective4 κ ι ρ * moment v).trace =
      ∑ S : Finset κ, ((-1 / 2 : ℂ) ^ S.card) * wordVal (objSites S) (Equiv.swap 0 3) v := by
  rw [objective4, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_permOp_moment, smul_eq_mul]

theorem objSites_comp (π : Equiv.Perm κ) (S : Finset κ) :
    (fun i => objSites S (π i)) = objSites (S.map π.symm.toEmbedding) := by
  funext i
  simp only [objSites, Finset.mem_map_equiv, Equiv.symm_symm]

theorem trace_objective4_gact (g : Equiv.Perm κ × Bool) (v : Fin 4 → (κ → ι) × ρ → ℂ) :
    (objective4 κ ι ρ * moment (fun k => gact g (v k))).trace =
      cj g.2 (objective4 κ ι ρ * moment v).trace := by
  rw [trace_objective4_moment, trace_objective4_moment, cj_sum]
  simp only [wordVal_gact, objSites_comp, cj_mul]
  have hc : ∀ S : Finset κ, cj g.2 ((-1 / 2 : ℂ) ^ S.card) = (-1 / 2 : ℂ) ^ S.card := by
    intro S
    rw [show ((-1 / 2 : ℂ) ^ S.card) = (((-1 / 2 : ℝ) ^ S.card : ℝ) : ℂ) by push_cast; ring,
      cj_ofReal]
  simp only [hc]
  refine (Equiv.sum_comp (Equiv.finsetCongr g.1.symm)
    (fun S => (-1 / 2 : ℂ) ^ S.card * cj g.2 (wordVal (objSites S) (Equiv.swap 0 3) v))).symm.trans ?_ |>.symm
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map]

/-- **(b) The objective.** `Tr[objective4 · Ŷ31] = q(∑_r |a_r⟩⟨b_r|)` for every lift. -/
theorem twirl_objective {a b : (κ → ι) × ρ → ℂ} (hab : IsLift a b) :
    (objective4 κ ι ρ * twirl .f31 a b).trace = (qfun (liftC a b) : ℂ) := by
  have hmem : objective4 κ ι ρ ∈ algT κ ι ρ ∅ :=
    Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (permOp_mem _ _)
  rw [trace_mul_twirl hmem]
  have hq := qfun_eq_trace_four a b (nsqC_of_vnormSq hab.2.1)
  have : ∀ g : Equiv.Perm κ × Bool,
      (objective4 κ ι ρ * Ymom .f31 (gact g a) (gact g b)).trace = (qfun (liftC a b) : ℂ) := by
    intro g
    rw [Ymom, famVec_gact, trace_objective4_gact]
    have e : (objective4 κ ι ρ * moment (famVec .f31 a b)).trace = (qfun (liftC a b) : ℂ) := by
      rw [famVec_f31]; exact hq.symm
    rw [e, cj_ofReal]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, avgW_mul_card, one_mul]

end Rep

/-- **End to end.** If the certificate gives `0 ≤ Re Tr[objective4 · Ŷ31]` for every lift,
then `q(C) ≥ 0` for every rank-`≤ 2` `C` (layer B's reduction plus (b)). -/
theorem qfun_nonneg_of_twirl {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (hH : 2 ≤ Fintype.card (κ → ι))
    (h : ∀ a b : (κ → ι) × Fin 2 → ℂ, IsLift a b →
      0 ≤ ((objective4 κ ι (Fin 2) * twirl .f31 a b).trace).re)
    (C : Matrix (κ → ι) (κ → ι) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C := by
  refine qfun_nonneg_of_trace_nonneg hH (fun a b hm ha hb => ?_) C hC
  have hab : IsLift a b := ⟨hm, ha, hb⟩
  have e1 := twirl_objective hab
  have e2 := qfun_eq_trace_four a b (nsqC_of_vnormSq ha)
  rw [← e2, ← e1]
  exact h a b hab

end WernerEndpoint

end

#print axioms WernerEndpoint.isLift_gact
#print axioms WernerEndpoint.twirl_spec
#print axioms WernerEndpoint.OpG_twirl
#print axioms WernerEndpoint.twirl_isHermitian
#print axioms WernerEndpoint.permOp_mul_moment
#print axioms WernerEndpoint.wordVal_bos_left
#print axioms WernerEndpoint.wordVal_bos_right
#print axioms WernerEndpoint.twirl_bos_left
#print axioms WernerEndpoint.twirl_bos_right
#print axioms WernerEndpoint.exists_real_invariant_rep
#print axioms WernerEndpoint.twirl_rep
#print axioms WernerEndpoint.twirl_ptrans_posSemidef
#print axioms WernerEndpoint.twirl_coupled_T3_posSemidef
#print axioms WernerEndpoint.twirl_coupled_T23_posSemidef
#print axioms WernerEndpoint.twirl_row
#print axioms WernerEndpoint.twirl_trace
#print axioms WernerEndpoint.twirl_contrast_row
#print axioms WernerEndpoint.twirl_row_31_22
#print axioms WernerEndpoint.twirl_row_22_13
#print axioms WernerEndpoint.wordVal_gact
#print axioms WernerEndpoint.twirl_objective
#print axioms WernerEndpoint.qfun_nonneg_of_twirl
