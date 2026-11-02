import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm

/-!
# Layer C: Brauer operators on one site (core: products and component certificates)

One site of the four-replica space is `(ℂ^α)^{⊗R}` (later `R = Fin 4`, `α = Fin d`); an operator
is a matrix indexed by colourings `x : R → α`. Its `2|R|` digit slots are `Sum.inl k` (row digit of
replica `k`) and `Sum.inr k` (column digit), as in `rearr` (L5); `z = Sum.elim x y`.

* `br α μ` for a slot map `μ : R ⊕ R → R ⊕ R` is the 0/1 operator
  `(br α μ) x y = [∀ q, z q = z (μ q)]` (a *Brauer operator*).
* `sP α p` is the permutation operator (`(sP α p) x y = [y = x ∘ p]`, the site factor of
  `permOp`), and `br_permMatch`: `sP α p = br α (permMatch p)`.
* `tauT T` swaps the two digits of each replica in `T` (the slot form of `Γ_T`, see
  `LayerC_Brauer.lean`).
* `br_mul_br`: the product of two Brauer operators is `|α|^c` times a Brauer operator, given a
  finite *component certificate* (`BrCert`): a root map with parent edges and ranks for the graph
  on the `3|R|` vertices (top, middle, bottom) whose edges are `μ` (top–middle) and `ν`
  (middle–bottom); `c` is the number of components inside the middle layer (closed loops).
  Every certificate condition is a finite check, so the concrete products (`LayerC_Walled.lean`)
  are checked by `decide`, and the identity then holds for every local dimension.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace WernerEndpoint

section Brauer

variable {R α : Type*} [Fintype R] [DecidableEq R] [Fintype α] [DecidableEq α]

variable (α) in
/-- The Brauer operator of a slot map `μ`: `(br α μ) x y = [∀ q, z q = z (μ q)]`, `z = Sum.elim x y`. -/
def br (μ : R ⊕ R → R ⊕ R) : Matrix (R → α) (R → α) ℂ :=
  Matrix.of fun x y => if ∀ q, Sum.elim x y q = Sum.elim x y (μ q) then 1 else 0

variable (α) in
/-- The permutation operator of one site: `(sP α p) x y = [y = x ∘ p]`. -/
def sP (p : Equiv.Perm R) : Matrix (R → α) (R → α) ℂ :=
  Matrix.of fun x y => if y = x ∘ p then 1 else 0

/-- The slot map (perfect matching) of the permutation `p`: column digit `k` is tied to row digit
`p k`. -/
def permMatch (p : Equiv.Perm R) : R ⊕ R → R ⊕ R
  | .inl j => .inr (p.symm j)
  | .inr k => .inl (p k)

theorem br_permMatch (p : Equiv.Perm R) : br α (permMatch p) = sP α p := by
  ext x y
  simp only [br, sP, Matrix.of_apply]
  by_cases h : y = x ∘ p
  · rw [if_pos h, if_pos]
    intro q
    cases q with
    | inl j => show x j = y (p.symm j); rw [h]; simp
    | inr k => show y k = x (p k); rw [h]; rfl
  · rw [if_neg h, if_neg]
    intro hq
    exact h (funext fun k => hq (.inr k))

/-- `τ_T`: the slot involution exchanging the row and column digit of every replica in `T`. -/
def tauT (T : Finset R) : R ⊕ R → R ⊕ R
  | .inl j => if j ∈ T then .inr j else .inl j
  | .inr j => if j ∈ T then .inl j else .inr j

theorem tauT_tauT (T : Finset R) (q : R ⊕ R) : tauT T (tauT T q) = q := by
  cases q with
  | inl j => by_cases h : j ∈ T <;> simp [tauT, h]
  | inr j => by_cases h : j ∈ T <;> simp [tauT, h]

/-- Slot maps that agree give the same Brauer operator. -/
theorem br_congr {μ ν : R ⊕ R → R ⊕ R} (h : ∀ q, μ q = ν q) : br α μ = br α ν := by
  rw [funext h]

/-! ### Products: the component certificate -/

/-- The three layers of a product `A * B`: top (row digits of `A`), middle (summed), bottom
(column digits of `B`). -/
abbrev Vtx (R : Type*) := R ⊕ R ⊕ R

/-- Slots of the first factor in the three-layer graph. -/
def e1 : R ⊕ R → Vtx R
  | .inl k => .inl k
  | .inr k => .inr (.inl k)

/-- Slots of the second factor. -/
def e2 : R ⊕ R → Vtx R
  | .inl k => .inr (.inl k)
  | .inr k => .inr (.inr k)

/-- Slots of the product. -/
def eo : R ⊕ R → Vtx R
  | .inl k => .inl k
  | .inr k => .inr (.inr k)

/-- The edges of the graph of `br μ * br ν`. -/
def edge (μ ν : R ⊕ R → R ⊕ R) : (R ⊕ R) ⊕ (R ⊕ R) → Vtx R × Vtx R
  | .inl q => (e1 q, e1 (μ q))
  | .inr q => (e2 q, e2 (ν q))

/-- A component certificate for `br μ * br ν = |α|^c • br λ`:
* `root` is constant along edges, idempotent, and every vertex that is not its own root has a
  parent edge `pe v` to a vertex of smaller `rank` with the same root;
* on the outer slots, `λ` pairs vertices with the same root, and each outer root is the vertex
  itself or its `λ`-partner;
* `c` is the number of middle vertices that are their own root. -/
def BrCert (μ ν lam : R ⊕ R → R ⊕ R) (root : Vtx R → Vtx R) (rank : Vtx R → ℕ)
    (pe : Vtx R → (R ⊕ R) ⊕ (R ⊕ R)) (c : ℕ) : Prop :=
  (∀ e, root (edge μ ν e).1 = root (edge μ ν e).2) ∧
  (∀ v, root (root v) = root v) ∧
  (∀ v, root v ≠ v →
    ((edge μ ν (pe v)).1 = v ∧ rank (edge μ ν (pe v)).2 < rank v ∧
        root (edge μ ν (pe v)).2 = root v) ∨
      ((edge μ ν (pe v)).2 = v ∧ rank (edge μ ν (pe v)).1 < rank v ∧
        root (edge μ ν (pe v)).1 = root v)) ∧
  (∀ q, root (eo q) = root (eo (lam q))) ∧
  (∀ q, root (eo q) = eo q ∨ root (eo q) = eo (lam q)) ∧
  c = (Finset.univ.filter fun k : R => root (.inr (.inl k)) = .inr (.inl k)).card

instance (μ ν lam : R ⊕ R → R ⊕ R) (root : Vtx R → Vtx R) (rank : Vtx R → ℕ)
    (pe : Vtx R → (R ⊕ R) ⊕ (R ⊕ R)) (c : ℕ) : Decidable (BrCert μ ν lam root rank pe c) := by
  unfold BrCert; infer_instance

/-- **Lemma A.** Under a certificate, a labelling respects every edge iff it is constant on
components (equal to its value at the root). -/
theorem edges_iff_root {μ ν lam : R ⊕ R → R ⊕ R} {root : Vtx R → Vtx R} {rank : Vtx R → ℕ}
    {pe : Vtx R → (R ⊕ R) ⊕ (R ⊕ R)} {c : ℕ} (h : BrCert μ ν lam root rank pe c)
    (L : Vtx R → α) :
    (∀ e, L (edge μ ν e).1 = L (edge μ ν e).2) ↔ ∀ v, L v = L (root v) := by
  obtain ⟨hE, -, hP, -⟩ := h
  constructor
  · intro hL
    suffices ∀ n, ∀ v, rank v = n → L v = L (root v) from fun v => this _ v rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hr : root v = v
      · rw [hr]
      · rcases hP v hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have e := hL (pe v)
          rw [h1] at e
          rw [e, ih _ (hv ▸ h2) _ rfl, h3]
        · have e := hL (pe v)
          rw [h1] at e
          rw [← e, ih _ (hv ▸ h2) _ rfl, h3]
  · intro hL e
    rw [hL (edge μ ν e).1, hL (edge μ ν e).2, hE e]

/-- **Lemma B (counting).** If `g k = some k'` means "`y k` is copied from `y k'`" (with `k'` a
free root) and `g k = none` means "`y k` is the fixed value `cv k`", the solutions are the free
colourings of the roots. -/
theorem card_fix_option {M β : Type*} [Fintype M] [DecidableEq M] [Fintype β] [DecidableEq β]
    (g : M → Option M) (cv : M → β) (hg : ∀ k k', g k = some k' → g k' = some k') :
    Fintype.card {y : M → β // ∀ k, y k = Option.elim (g k) (cv k) y} =
      Fintype.card β ^ Fintype.card {k // g k = some k} := by
  let extF : ({k // g k = some k} → β) → M → β := fun f k =>
    if h : g k = some k then f ⟨k, h⟩ else cv k
  have hext : ∀ f k k', g k' = some k → Option.elim (g k) (cv k) (extF f) = extF f k := by
    intro f k k' hk
    rw [hg k' k hk]
    rfl
  let e : {y : M → β // ∀ k, y k = Option.elim (g k) (cv k) y} ≃ ({k // g k = some k} → β) :=
    { toFun := fun y k => y.1 k.1
      invFun := fun f => ⟨fun k => Option.elim (g k) (cv k) (extF f), by
        intro k
        cases hk : g k with
        | none => simp [hk]
        | some k' => simp only [hk, Option.elim_some]; exact (hext f k' k hk).symm⟩
      left_inv := fun y => by
        apply Subtype.ext
        funext k
        have hy := y.2 k
        cases hk : g k with
        | none => simp only [hk, Option.elim_none] at hy ⊢; exact hy.symm
        | some k' =>
          have h' := hg k k' hk
          simp only [hk, Option.elim_some] at hy ⊢
          simp only [extF, h', dif_pos]
          exact hy.symm
      right_inv := fun f => by
        funext k
        obtain ⟨k, h⟩ := k
        show Option.elim (g k) (cv k) (extF f) = f ⟨k, h⟩
        rw [h]
        simp only [Option.elim_some, extF, h, dif_pos] }
  rw [Fintype.card_congr e, Fintype.card_fun]

theorem ite_one_mul_ite_one (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then (1 : ℂ) else 0) * if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The labelling of the three layers. -/
def lab (x y z : R → α) : Vtx R → α := Sum.elim x (Sum.elim y z)

theorem lab_e1 (x y z : R → α) (q : R ⊕ R) : lab x y z (e1 q) = Sum.elim x y q := by
  cases q <;> rfl

theorem lab_e2 (x y z : R → α) (q : R ⊕ R) : lab x y z (e2 q) = Sum.elim y z q := by
  cases q <;> rfl

theorem lab_eo (x y z : R → α) (q : R ⊕ R) : lab x y z (eo q) = Sum.elim x z q := by
  cases q <;> rfl

/-- Which middle vertex (if any) a vertex is. -/
def midOf : Vtx R → Option R
  | .inr (.inl k) => some k
  | _ => none

/-- The label of an outer vertex (`a0` for middle vertices, never used). -/
def outerLab (x z : R → α) (a0 : α) : Vtx R → α
  | .inl j => x j
  | .inr (.inl _) => a0
  | .inr (.inr j) => z j

theorem lab_eq_elim (x y z : R → α) (a0 : α) (w : Vtx R) :
    lab x y z w = Option.elim (midOf w) (outerLab x z a0 w) y := by
  rcases w with j | j | j <;> rfl

theorem midOf_eq_some {w : Vtx R} {k : R} : midOf w = some k ↔ w = .inr (.inl k) := by
  rcases w with j | j | j <;> simp [midOf]

/-- **Products of Brauer operators.** Under a component certificate,
`br μ * br ν = |α|^c • br λ`. Holds for every local dimension `|α| ≥ 1`. -/
theorem br_mul_br [Nonempty α] {μ ν lam : R ⊕ R → R ⊕ R} {root : Vtx R → Vtx R}
    {rank : Vtx R → ℕ} {pe : Vtx R → (R ⊕ R) ⊕ (R ⊕ R)} {c : ℕ}
    (h : BrCert μ ν lam root rank pe c) :
    br α μ * br α ν = ((Fintype.card α ^ c : ℕ) : ℂ) • br α lam := by
  obtain a0 : α := Classical.arbitrary α
  have hc := h.2.2.2.2.2
  have hidem := h.2.1
  have hlr := h.2.2.2.1
  have hlc := h.2.2.2.2.1
  ext x z
  simp only [Matrix.mul_apply, br, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    ite_one_mul_ite_one]
  -- the outer condition
  set O : Prop := ∀ q, Sum.elim x z q = Sum.elim x z (lam q) with hOdef
  let g : R → Option R := fun k => midOf (root (.inr (.inl k)))
  let cv : R → α := fun k => outerLab x z a0 (root (.inr (.inl k)))
  have key : ∀ y : R → α,
      ((∀ q, Sum.elim x y q = Sum.elim x y (μ q)) ∧ ∀ q, Sum.elim y z q = Sum.elim y z (ν q)) ↔
        O ∧ ∀ k, y k = Option.elim (g k) (cv k) y := by
    intro y
    have h1 : ((∀ q, Sum.elim x y q = Sum.elim x y (μ q)) ∧
        ∀ q, Sum.elim y z q = Sum.elim y z (ν q)) ↔
        ∀ e, lab x y z (edge μ ν e).1 = lab x y z (edge μ ν e).2 := by
      simp only [Sum.forall, edge, lab_e1, lab_e2]
    rw [h1, edges_iff_root h]
    constructor
    · intro hv
      refine ⟨fun q => ?_, fun k => ?_⟩
      · have e1' := hv (eo q)
        have e2' := hv (eo (lam q))
        rw [lab_eo] at e1' e2'
        rw [e1', e2', hlr q]
      · have := hv (.inr (.inl k))
        rw [lab_eq_elim x y z a0 (root _)] at this
        exact this
    · rintro ⟨hO, hM⟩ v
      rcases v with j | j | j
      · rcases hlc (.inl j) with h' | h'
        · exact congrArg (lab x y z) h'.symm
        · rw [show root (.inl j) = eo (lam (.inl j)) from h', lab_eo]
          exact hO (.inl j)
      · rw [lab_eq_elim x y z a0 (root _)]
        exact hM j
      · rcases hlc (.inr j) with h' | h'
        · exact congrArg (lab x y z) h'.symm
        · rw [show root (.inr (.inr j)) = eo (lam (.inr j)) from h', lab_eo]
          exact hO (.inr j)
  rw [Finset.sum_congr rfl fun y _ => if_congr (key y) rfl rfl]
  have hg : ∀ k k', g k = some k' → g k' = some k' := by
    intro k k' hk
    have hr : root (.inr (.inl k)) = .inr (.inl k') := midOf_eq_some.mp hk
    show midOf (root (.inr (.inl k'))) = some k'
    rw [← hr, hidem, hr]
    rfl
  have hcount : Fintype.card {k // g k = some k} = c := by
    rw [hc, Fintype.card_subtype]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    exact midOf_eq_some
  by_cases hO : O
  · have hs : ∀ y : R → α, (if O ∧ (∀ k, y k = Option.elim (g k) (cv k) y) then (1 : ℂ) else 0) =
        if (∀ k, y k = Option.elim (g k) (cv k) y) then 1 else 0 :=
      fun y => if_congr ⟨fun h => h.2, fun h => ⟨hO, h⟩⟩ rfl rfl
    rw [Finset.sum_congr rfl fun y _ => hs y, Finset.sum_boole, if_pos hO, mul_one, ← hcount,
      ← card_fix_option g cv hg, Fintype.card_subtype]
  · rw [if_neg hO, mul_zero]
    exact Finset.sum_eq_zero fun y _ => if_neg fun h => hO h.1

end Brauer

end WernerEndpoint

#print axioms WernerEndpoint.br_permMatch
#print axioms WernerEndpoint.edges_iff_root
#print axioms WernerEndpoint.card_fix_option
#print axioms WernerEndpoint.br_mul_br
