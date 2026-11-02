import WernerEndpoint.LayerC_Walled
import WernerEndpoint.LayerC_Trace
import WernerEndpoint.LayerC_Projection

/-!
# Layer C: site factorisation, the algebras `𝒜_T`, and L6 on the four-replica space

The four-replica space has multi-indices `X : Fin 4 → (κ → ι) × ρ` (replica-major, as in layer B).
`siteDig X i : Fin 4 → ι` (the digits of site `i` in the four replicas) and `qDig X : Fin 4 → ρ`
(the qubit digits) split `X` over the sites (`splitIdx` of `LayerC_Trace.lean`, the
`Equiv.piComm`-style reindexing).

* `sprod A B = ⊗_i A_i ⊗ B` (one operator per site and one for the qubit, each on four replicas).
  **Site factorisation:** `permOp_eq_sprod` (`P_{(w,wq)} = ⊗_i P_{w_i} ⊗ P_{wq}`),
  `ptrans_sprod` (`Γ_T` of the four-replica space is `Γ_T` on every site),
  `rearr_sprod` (a literal rearrangement `σ` of the four-replica space is `σ` on every site),
  `sprod_mul`, `sprod_conjTranspose`, `sprod_smul`.
* `PT T t = Γ_T(P_t)` for a diagram tuple `t = (w, wq) : Tup κ`, and
  `algT T = span{Γ_T(P_t)}` (so `algT ∅ = span{P_t}` is the algebra of the twirl).
  `isStarAlg_algT`: for every cut of the verifier (`IsCut T`) and local dimensions `|ι|, |ρ| ≥ 1`,
  `algT T` is a unital `*`-subalgebra (walled closure, site by site).
* **L6 on the four-replica space** (`rearr_PT_T3_31` …): `rearr σ (P_{(w,wq)}) =
  Γ_T(P_{(m ∘ w, m wq)})` with the same table map `m` at every site and at the qubit.
* Transport of the projection: `isHSProj_ptrans` (`Γ_T` maps `algT ∅` onto `algT T`) and
  `isHSProj_rearr_*` (each of the six tables maps `algT ∅` onto `algT T`).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace WernerEndpoint

section Sites

variable {κ ι ρ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ]

/-- The digits of site `i` in the four replicas. -/
def siteDig (X : Fin 4 → (κ → ι) × ρ) (i : κ) : Fin 4 → ι := fun k => (X k).1 i

/-- The qubit digits in the four replicas. -/
def qDig (X : Fin 4 → (κ → ι) × ρ) : Fin 4 → ρ := fun k => (X k).2

/-- The site product `⊗_i A_i ⊗ B` on the four-replica space. -/
def sprod (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ) (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  Matrix.of fun X Y => (∏ i, A i (siteDig X i) (siteDig Y i)) * B (qDig X) (qDig Y)

theorem eq_permIdx_iff (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4))
    (X Y : Fin 4 → (κ → ι) × ρ) :
    Y = permIdx w wq X ↔ (∀ i, siteDig Y i = siteDig X i ∘ w i) ∧ qDig Y = qDig X ∘ wq := by
  constructor
  · rintro rfl
    exact ⟨fun i => rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext k
    refine Prod.ext (funext fun i => ?_) ?_
    · exact congrFun (h1 i) k
    · exact congrFun h2 k

/-- **Site factorisation of the permutation operators.** -/
theorem permOp_eq_sprod (w : κ → Equiv.Perm (Fin 4)) (wq : Equiv.Perm (Fin 4)) :
    permOp ι ρ w wq = sprod (fun i => sP ι (w i)) (sP ρ wq) := by
  ext X Y
  simp only [permOp, sprod, sP, Matrix.of_apply, Fintype.prod_boole, ite_mul, one_mul, zero_mul]
  by_cases h : Y = permIdx w wq X
  · rw [if_pos h, if_pos ((eq_permIdx_iff w wq X Y).mp h).1,
      if_pos ((eq_permIdx_iff w wq X Y).mp h).2]
  · rw [if_neg h]
    by_cases h1 : ∀ i, siteDig Y i = siteDig X i ∘ w i
    · rw [if_pos h1, if_neg fun h2 => h ((eq_permIdx_iff w wq X Y).mpr ⟨h1, h2⟩)]
    · rw [if_neg h1]

theorem siteDig_ptrans (T : Finset (Fin 4)) (X Y : Fin 4 → (κ → ι) × ρ) (i : κ) :
    siteDig (fun r => if r ∈ T then Y r else X r) i =
      fun r => if r ∈ T then siteDig Y i r else siteDig X i r := by
  funext r
  by_cases h : r ∈ T <;> simp [siteDig, h]

theorem qDig_ptrans (T : Finset (Fin 4)) (X Y : Fin 4 → (κ → ι) × ρ) :
    qDig (fun r => if r ∈ T then Y r else X r) =
      fun r => if r ∈ T then qDig Y r else qDig X r := by
  funext r
  by_cases h : r ∈ T <;> simp [qDig, h]

/-- **Site factorisation of the partial transpose.** -/
theorem ptrans_sprod (T : Finset (Fin 4)) (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ)
    (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (sprod A B) =
      sprod (fun i => ptrans (ι := fun _ : Fin 4 => ι) T (A i))
        (ptrans (ι := fun _ : Fin 4 => ρ) T B) := by
  ext X Y
  simp only [ptrans, sprod, Matrix.of_apply, siteDig_ptrans, qDig_ptrans]

theorem siteDig_rearr (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (X Y : Fin 4 → (κ → ι) × ρ) (i : κ)
    (b : Fin 4 → Fin 4 ⊕ Fin 4) :
    siteDig (fun s => Sum.elim X Y (b s)) i = fun s => Sum.elim (siteDig X i) (siteDig Y i) (b s) := by
  funext s
  show (Sum.elim X Y (b s)).1 i = Sum.elim (siteDig X i) (siteDig Y i) (b s)
  cases b s <;> rfl

theorem qDig_rearr (X Y : Fin 4 → (κ → ι) × ρ) (b : Fin 4 → Fin 4 ⊕ Fin 4) :
    qDig (fun s => Sum.elim X Y (b s)) = fun s => Sum.elim (qDig X) (qDig Y) (b s) := by
  funext s
  show (Sum.elim X Y (b s)).2 = Sum.elim (qDig X) (qDig Y) (b s)
  cases b s <;> rfl

/-- **Site factorisation of a literal rearrangement:** the same slot map at every site and at the
qubit. -/
theorem rearr_sprod (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ)
    (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    rearr σ (sprod A B) = sprod (fun i => rearr σ (A i)) (rearr σ B) := by
  ext X Y
  simp only [rearr, sprod, Matrix.of_apply, siteDig_rearr σ, qDig_rearr]

theorem sprod_mul (A A' : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ) (B B' : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    sprod A B * sprod A' B' = sprod (fun i => A i * A' i) (B * B') := by
  ext X Z
  simp only [sprod, Matrix.mul_apply, Matrix.of_apply]
  rw [← (splitIdx (R := Fin 4) (κ := κ) (ι := ι) (ρ := ρ)).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ∀ i, siteDig (splitIdx.symm (F, g) : Fin 4 → (κ → ι) × ρ) i = F i := fun i => rfl
  have h2 : qDig (splitIdx.symm (F, g) : Fin 4 → (κ → ι) × ρ) = g := rfl
  simp only [h1, h2]
  rw [show ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) from fun a b c d => by ring,
    ← Finset.prod_mul_distrib]

theorem sprod_conjTranspose (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ)
    (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    (sprod A B)ᴴ = sprod (fun i => (A i)ᴴ) Bᴴ := by
  ext X Y
  simp only [sprod, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_prod]

theorem sprod_smul (c : κ → ℂ) (d : ℂ) (A : κ → Matrix (Fin 4 → ι) (Fin 4 → ι) ℂ)
    (B : Matrix (Fin 4 → ρ) (Fin 4 → ρ) ℂ) :
    sprod (fun i => c i • A i) (d • B) = ((∏ i, c i) * d) • sprod A B := by
  ext X Y
  simp only [sprod, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  ring

theorem ptrans_one' {R : Type*} [Fintype R] [DecidableEq R] {β : Type*} [DecidableEq β]
    (T : Finset R) :
    ptrans (ι := fun _ : R => β) T (1 : Matrix (R → β) (R → β) ℂ) = 1 := by
  ext x y
  simp only [ptrans, Matrix.of_apply, Matrix.one_apply]
  have : ((fun r => if r ∈ T then y r else x r) = fun r => if r ∈ T then x r else y r) ↔ x = y := by
    constructor
    · intro h
      funext r
      have := congrFun h r
      by_cases hr : r ∈ T <;> simp [hr] at this <;> [exact this.symm; exact this]
    · rintro rfl
      rfl
  exact if_congr this rfl rfl

theorem ptrans_conjTranspose {R : Type*} [DecidableEq R] {β : Type*} (T : Finset R)
    (A : Matrix (R → β) (R → β) ℂ) :
    (ptrans (ι := fun _ : R => β) T A)ᴴ = ptrans (ι := fun _ : R => β) T Aᴴ := by
  ext x y
  simp only [ptrans, Matrix.conjTranspose_apply, Matrix.of_apply]

/-! ### The algebras `𝒜_T` -/

variable (κ) in
/-- Diagram tuples `(w, wq)`: one permutation of the replicas per site and one for the qubit. -/
abbrev Tup := (κ → Equiv.Perm (Fin 4)) × Equiv.Perm (Fin 4)

variable (ι ρ) in
/-- `Γ_T(P_t)` on the four-replica space. -/
def PT (T : Finset (Fin 4)) (t : Tup κ) : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ :=
  ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T (permOp ι ρ t.1 t.2)

variable (κ ι ρ) in
/-- `𝒜_T = span{Γ_T(P_t)}`. `algT ∅ = span{P_t}` is the range of the twirl. -/
def algT (T : Finset (Fin 4)) : Submodule ℂ (Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ) :=
  Submodule.span ℂ (Set.range (PT (κ := κ) ι ρ T))

theorem PT_mem (T : Finset (Fin 4)) (t : Tup κ) : PT ι ρ T t ∈ algT κ ι ρ T :=
  Submodule.subset_span ⟨t, rfl⟩

theorem PT_empty (t : Tup κ) : PT ι ρ ∅ t = permOp ι ρ t.1 t.2 := by
  ext X Y
  simp [PT, ptrans]

theorem PT_eq_sprod (T : Finset (Fin 4)) (t : Tup κ) :
    PT ι ρ T t = sprod (fun i => ptrans (ι := fun _ : Fin 4 => ι) T (sP ι (t.1 i)))
      (ptrans (ι := fun _ : Fin 4 => ρ) T (sP ρ t.2)) := by
  rw [PT, permOp_eq_sprod, ptrans_sprod]

theorem PT_mul_PT [Nonempty ι] [Nonempty ρ] {T : Finset (Fin 4)} (hT : IsCut T) (t t' : Tup κ) :
    ∃ (u : Tup κ) (c : ℂ), PT ι ρ T t * PT ι ρ T t' = c • PT ι ρ T u := by
  have hs := fun i => ptrans_sP_mul ι hT (t.1 i) (t'.1 i)
  choose u c hu using hs
  obtain ⟨uq, cq, huq⟩ := ptrans_sP_mul ρ hT t.2 t'.2
  refine ⟨(u, uq), (∏ i, ((Fintype.card ι ^ c i : ℕ) : ℂ)) * ((Fintype.card ρ ^ cq : ℕ) : ℂ), ?_⟩
  rw [PT_eq_sprod, PT_eq_sprod, sprod_mul, PT_eq_sprod]
  simp only [hu, huq]
  exact sprod_smul _ _ _ _

theorem PT_conjTranspose (T : Finset (Fin 4)) (t : Tup κ) :
    (PT ι ρ T t)ᴴ = PT ι ρ T (fun i => (t.1 i)⁻¹, t.2⁻¹) := by
  rw [PT, PT, ptrans_conjTranspose, permOp_conjTranspose]

theorem one_eq_PT (T : Finset (Fin 4)) : (1 : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ) =
    PT ι ρ T (fun _ => 1, 1) := by
  rw [PT, permOp_one, ptrans_one']

/-- `𝒜_T` is a unital `*`-subalgebra once products of generators are multiples of generators. -/
theorem isStarAlg_algT_of_mul {T : Finset (Fin 4)}
    (hmul : ∀ t t' : Tup κ, ∃ (u : Tup κ) (c : ℂ), PT ι ρ T t * PT ι ρ T t' = c • PT ι ρ T u) :
    IsStarAlg (algT κ ι ρ T) where
  one_mem := by rw [one_eq_PT T]; exact PT_mem T _
  mul_mem := by
    intro A B hA hB
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      induction hB using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨t', rfl⟩ := hy
        obtain ⟨u, c, h⟩ := hmul t t'
        rw [h]
        exact Submodule.smul_mem _ _ (PT_mem T u)
      | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [Matrix.mul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ _ hy
    | zero => rw [Matrix.zero_mul]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_mul]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ _ hx
  star_mem := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [PT_conjTranspose]
      exact PT_mem T _
    | zero => rw [conjTranspose_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [conjTranspose_add]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ hx

/-- **`𝒜_T` is a unital `*`-subalgebra** for every cut of the verifier and every local
dimension. -/
theorem isStarAlg_algT [Nonempty ι] [Nonempty ρ] {T : Finset (Fin 4)} (hT : IsCut T) :
    IsStarAlg (algT κ ι ρ T) :=
  isStarAlg_algT_of_mul (PT_mul_PT hT)

/-- `span{P_t}` is a unital `*`-subalgebra (any local dimensions). -/
theorem isStarAlg_algT_empty : IsStarAlg (algT κ ι ρ ∅) :=
  isStarAlg_algT_of_mul fun t t' =>
    ⟨(fun i => t.1 i * t'.1 i, t.2 * t'.2), 1, by rw [PT_empty, PT_empty, PT_empty, permOp_mul, one_smul]⟩

theorem algT_star_mem {T : Finset (Fin 4)} {A : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ}
    (hA : A ∈ algT κ ι ρ T) : Aᴴ ∈ algT κ ι ρ T := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [PT_conjTranspose]
    exact PT_mem T _
  | zero => rw [conjTranspose_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [conjTranspose_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ hx

/-! ### Transport along `Γ_T` and along the six rearrangements -/

/-- A linear map of the four-replica space that carries each `P_t` into `algT T` and is onto it
on the spanning set carries `algT ∅` onto `algT T`. -/
theorem map_algT_of_PT {T : Finset (Fin 4)}
    (φ : Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ)
    (f : Tup κ → Tup κ) (hf : ∀ t, φ (PT ι ρ ∅ t) = PT ι ρ T (f t)) (hsurj : Function.Surjective f) :
    (∀ A ∈ algT κ ι ρ ∅, φ A ∈ algT κ ι ρ T) ∧
      ∀ A' ∈ algT κ ι ρ T, ∃ A ∈ algT κ ι ρ ∅, φ A = A' := by
  constructor
  · intro A hA
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [hf]
      exact PT_mem T _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro A' hA'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t', rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hsurj t'
      exact ⟨_, PT_mem ∅ t, hf t⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero φ⟩
    | add x z _ _ hx hz =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add φ a b⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, map_smul φ c a⟩

variable (κ ι ρ) in
/-- `Γ_T` on the four-replica space as a linear map. -/
def ptransL (T : Finset (Fin 4)) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ where
  toFun := ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T
  map_add' A B := by ext X Y; simp [ptrans]
  map_smul' c A := by ext X Y; simp [ptrans]

variable (κ ι ρ) in
/-- A literal rearrangement on the four-replica space as a linear map. -/
def rearrL (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) :
    Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → (κ → ι) × ρ) (Fin 4 → (κ → ι) × ρ) ℂ where
  toFun := rearr σ
  map_add' := rearr_add σ
  map_smul' := rearr_smul σ

/-- The index involution of `Γ_T`. -/
def ptransIdx {R β : Type*} [DecidableEq R] (T : Finset R) : (R → β) × (R → β) ≃ (R → β) × (R → β) :=
  Function.Involutive.toPerm
    (fun p => (fun r => if r ∈ T then p.2 r else p.1 r, fun r => if r ∈ T then p.1 r else p.2 r))
    (fun p => by
      refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;> by_cases h : r ∈ T <;> simp [h])

theorem hs_ptrans {R β : Type*} [Fintype R] [DecidableEq R] [Fintype β] [DecidableEq β]
    (T : Finset R) (A B : Matrix (R → β) (R → β) ℂ) :
    hs (ptrans (ι := fun _ : R => β) T A) (ptrans (ι := fun _ : R => β) T B) = hs A B :=
  hs_reindex (ptransIdx T) A B

/-- The index bijection of a literal rearrangement. -/
def rearrIdx {R β : Type*} (σ : R ⊕ R ≃ R ⊕ R) : (R → β) × (R → β) ≃ (R → β) × (R → β) where
  toFun p := (fun s => Sum.elim p.1 p.2 (σ (.inl s)), fun s => Sum.elim p.1 p.2 (σ (.inr s)))
  invFun p := (fun s => Sum.elim p.1 p.2 (σ.symm (.inl s)), fun s => Sum.elim p.1 p.2 (σ.symm (.inr s)))
  left_inv p := by
    have h : ∀ q, Sum.elim (fun s => Sum.elim p.1 p.2 (σ (.inl s)))
        (fun s => Sum.elim p.1 p.2 (σ (.inr s))) q = Sum.elim p.1 p.2 (σ q) := by
      intro q; cases q <;> rfl
    refine Prod.ext (funext fun s => ?_) (funext fun s => ?_)
    · show Sum.elim _ _ (σ.symm (.inl s)) = p.1 s
      rw [h, Equiv.apply_symm_apply]; rfl
    · show Sum.elim _ _ (σ.symm (.inr s)) = p.2 s
      rw [h, Equiv.apply_symm_apply]; rfl
  right_inv p := by
    have h : ∀ q, Sum.elim (fun s => Sum.elim p.1 p.2 (σ.symm (.inl s)))
        (fun s => Sum.elim p.1 p.2 (σ.symm (.inr s))) q = Sum.elim p.1 p.2 (σ.symm q) := by
      intro q; cases q <;> rfl
    refine Prod.ext (funext fun s => ?_) (funext fun s => ?_)
    · show Sum.elim _ _ (σ (.inl s)) = p.1 s
      rw [h, Equiv.symm_apply_apply]; rfl
    · show Sum.elim _ _ (σ (.inr s)) = p.2 s
      rw [h, Equiv.symm_apply_apply]; rfl

theorem hs_rearr {R β : Type*} [Fintype R] [DecidableEq R] [Fintype β] [DecidableEq β]
    (σ : R ⊕ R ≃ R ⊕ R) (A B : Matrix (R → β) (R → β) ℂ) :
    hs (rearr σ A) (rearr σ B) = hs A B :=
  hs_reindex (rearrIdx σ) A B

/-- **Transport along `Γ_T`.** If `Z` is the projection of `Y` onto `algT ∅`, then `Γ_T Z` is the
projection of `Γ_T Y` onto `algT T`. -/
theorem isHSProj_ptrans (T : Finset (Fin 4)) {Y Z : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ}
    (h : IsHSProj (algT κ ι ρ ∅) Y Z) :
    IsHSProj (algT κ ι ρ T) (ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T Y)
      (ptrans (ι := fun _ : Fin 4 => (κ → ι) × ρ) T Z) := by
  obtain ⟨hmem, hsurj⟩ := map_algT_of_PT (ι := ι) (ρ := ρ) (T := T) (ptransL κ ι ρ T) id
    (fun t => by
      show ptrans _ (PT ι ρ ∅ t) = PT ι ρ T t
      rw [PT_empty]; rfl) Function.surjective_id
  exact h.map (ptransL κ ι ρ T) (fun Y Z => map_sub _ Y Z)
    (fun A B hAB => by
      show hs (ptrans _ A) (ptrans _ B) = 0
      rw [hs_ptrans]; exact hAB) hmem hsurj

/-! ### L6 on the four-replica space -/

/-- A table map `m` (in `PERMS` indices) as a map of permutations. -/
def permMap (m : Fin 24 → Fin 24) (p : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 4) :=
  permTab (m (Classical.choose (permTab_surj p)))

theorem permMap_permTab_choose (p : Equiv.Perm (Fin 4)) :
    permTab (Classical.choose (permTab_surj p)) = p := Classical.choose_spec (permTab_surj p)

theorem permTab_injective : Function.Injective permTab := by
  intro a b hab
  have : ∀ k, permFun a k = permFun b k := fun k => congrArg (fun e => e k) hab
  revert this; revert a b; decide

/-- On listed permutations the table map is the table: `permMap m (PERMS[i]) = PERMS[m i]`. -/
theorem permMap_permTab (m : Fin 24 → Fin 24) (i : Fin 24) : permMap m (permTab i) = permTab (m i) := by
  unfold permMap
  rw [permTab_injective (Classical.choose_spec (permTab_surj (permTab i)))]

theorem permMap_surj {m : Fin 24 → Fin 24} (hm : ∀ j, ∃ i, m i = j) :
    Function.Surjective (permMap m) := by
  intro q
  obtain ⟨j, rfl⟩ := permTab_surj q
  obtain ⟨i, rfl⟩ := hm j
  exact ⟨permTab i, permMap_permTab m i⟩

/-- The diagram tuple map of a table: the same `m` at every site and at the qubit. -/
def tupMap (m : Fin 24 → Fin 24) (t : Tup κ) : Tup κ := (fun i => permMap m (t.1 i), permMap m t.2)

theorem tupMap_surj {m : Fin 24 → Fin 24} (hm : ∀ j, ∃ i, m i = j) :
    Function.Surjective (tupMap (κ := κ) m) := by
  intro t'
  choose f hf using permMap_surj hm
  exact ⟨(fun i => f (t'.1 i), f t'.2), Prod.ext (funext fun i => hf _) (hf _)⟩

/-- Site-level L6 for all permutations. -/
theorem rearr_sP_permMap {α : Type*} [Fintype α] [DecidableEq α] (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4)
    (T : Finset (Fin 4)) (m : Fin 24 → Fin 24)
    (hσ : ∀ i, rearr σ (sP α (permTab i)) = ptrans (ι := fun _ : Fin 4 => α) T (sP α (permTab (m i))))
    (p : Equiv.Perm (Fin 4)) :
    rearr σ (sP α p) = ptrans (ι := fun _ : Fin 4 => α) T (sP α (permMap m p)) := by
  conv_lhs => rw [← permMap_permTab_choose p]
  exact hσ _

/-- **L6 on the four-replica space**, from the site-level identities (same table at every site
and at the qubit): `rearr σ (P_t) = Γ_T(P_{m t})`. -/
theorem rearr_permOp_of_sites (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (T : Finset (Fin 4))
    (m : Fin 24 → Fin 24)
    (hι : ∀ i, rearr σ (sP ι (permTab i)) = ptrans (ι := fun _ : Fin 4 => ι) T (sP ι (permTab (m i))))
    (hρ : ∀ i, rearr σ (sP ρ (permTab i)) = ptrans (ι := fun _ : Fin 4 => ρ) T (sP ρ (permTab (m i))))
    (t : Tup κ) : rearr σ (permOp ι ρ t.1 t.2) = PT ι ρ T (tupMap m t) := by
  rw [permOp_eq_sprod, rearr_sprod, PT_eq_sprod]
  simp only [tupMap]
  rw [rearr_sP_permMap σ T m hρ]
  congr 1
  funext i
  exact rearr_sP_permMap σ T m hι _

/-- **Transport along a rearrangement.** If `rearr σ (P_t) = Γ_T(P_{f t})` with `f` onto, the
projection onto `algT ∅` is carried to the projection onto `algT T`. -/
theorem isHSProj_rearr (σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4) (T : Finset (Fin 4)) (f : Tup κ → Tup κ)
    (hf : ∀ t, rearr σ (permOp ι ρ t.1 t.2) = PT ι ρ T (f t)) (hsurj : Function.Surjective f)
    {Y Z : Matrix (Fin 4 → (κ → ι) × ρ) _ ℂ} (h : IsHSProj (algT κ ι ρ ∅) Y Z) :
    IsHSProj (algT κ ι ρ T) (rearr σ Y) (rearr σ Z) := by
  obtain ⟨hmem, hsurj'⟩ := map_algT_of_PT (ι := ι) (ρ := ρ) (T := T) (rearrL κ ι ρ σ) f
    (fun t => by
      show rearr σ (PT ι ρ ∅ t) = PT ι ρ T (f t)
      rw [PT_empty]; exact hf t) hsurj
  exact h.map (rearrL κ ι ρ σ) (fun Y Z => map_sub _ Y Z)
    (fun A B hAB => by
      show hs (rearr σ A) (rearr σ B) = 0
      rw [hs_rearr]; exact hAB) hmem hsurj'

end Sites

end WernerEndpoint

end

#print axioms WernerEndpoint.permOp_eq_sprod
#print axioms WernerEndpoint.ptrans_sprod
#print axioms WernerEndpoint.rearr_sprod
#print axioms WernerEndpoint.sprod_mul
#print axioms WernerEndpoint.isStarAlg_algT
#print axioms WernerEndpoint.isStarAlg_algT_empty
#print axioms WernerEndpoint.isHSProj_ptrans
#print axioms WernerEndpoint.rearr_permOp_of_sites
#print axioms WernerEndpoint.isHSProj_rearr
#print axioms WernerEndpoint.tupMap_surj
#print axioms WernerEndpoint.permMap_permTab
