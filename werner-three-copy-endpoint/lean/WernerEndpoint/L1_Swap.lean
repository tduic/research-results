import WernerEndpoint.LayerB_Basic

/-!
# L1: the swap identity (layer B of `exact_certificate_d5/LEAN_PLAN.md`)

Sites are indexed by `κ` (later `Fin 3`), the local space by `ι` (later `Fin d`), so a vector of
`(ℂ^d)^{⊗3}` is a function of the multi-index `x : κ → ι`, and an operator `C` is a
`Matrix (κ → ι) (κ → ι) ℂ`.

* `partialTrace S C` is `Tr_S C`, the partial trace over the sites in `S`; it is an operator on the
  remaining sites, indexed by `{r // r ∉ S} → ι`:
  `(Tr_S C) u v = ∑_{z : S → ι} C (merge S u z) (merge S v z)`.
* `qfun C = ∑_{S ⊆ κ} (-1/2)^{|S|} ‖Tr_S C‖²_F` (README §"The problem", `q = q_{1/2}`).
* `liftC a b = ∑_r |a_r⟩⟨b_r|` for `a b : H × ρ → ℂ`: `liftC a b x y = ∑_r a (x, r) * conj (b (y, r))`.
* Two replicas of `H × ρ` (`H = κ → ι`, `ρ` the qubit): `twoRep a b = a ⊗ b`, and
  `swapOp ι ρ S = F_Q ∏_{i ∈ S} F_i` swaps the qubit and the sites in `S` between the replicas.

**L1** (`frobSq_partialTrace_liftC`): `‖Tr_S (liftC a b)‖² = ⟨a⊗b | F_Q ∏_{i∈S} F_i | a⊗b⟩`.
Consequently (`qfun_liftC_eq_trace`) `q(liftC a b) = Tr[W₂ · |a⊗b⟩⟨a⊗b|]` with the objective word
`W₂ = ∑_S (-1/2)^{|S|} F_Q ∏_{i∈S} F_i` (`objective2`).  The four-replica form
`q = Tr[W · Y31]` is in `L1_FourReplica.lean`.

Homogeneity: `qfun_smul : q(t • C) = |t|² q(C)`.
-/

open Matrix

noncomputable section

namespace WernerEndpoint

section PartialTrace

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- The multi-index that equals `u` off `S` and `z` on `S`. -/
def merge (S : Finset κ) (u : {r // r ∉ S} → ι) (z : {r // r ∈ S} → ι) : κ → ι :=
  fun r => if h : r ∈ S then z ⟨r, h⟩ else u ⟨r, h⟩

/-- The partial trace `Tr_S C` over the sites in `S`, an operator on the sites not in `S`. -/
def partialTrace (S : Finset κ) (C : Matrix (κ → ι) (κ → ι) ℂ) :
    Matrix ({r // r ∉ S} → ι) ({r // r ∉ S} → ι) ℂ :=
  Matrix.of fun u v => ∑ z : {r // r ∈ S} → ι, C (merge S u z) (merge S v z)

/-- `q(C) = ∑_{S} (-1/2)^{|S|} ‖Tr_S C‖²_F`. -/
def qfun (C : Matrix (κ → ι) (κ → ι) ℂ) : ℝ :=
  ∑ S : Finset κ, (-1 / 2 : ℝ) ^ S.card * frobSq (partialTrace S C)

/-- Summing over multi-indices = summing over the part off `S` and the part on `S`. -/
theorem sum_merge (S : Finset κ) (f : (κ → ι) → ℂ) :
    ∑ x, f x = ∑ u : {r // r ∉ S} → ι, ∑ z : {r // r ∈ S} → ι, f (merge S u z) := by
  let e : ({r // r ∉ S} → ι) × ({r // r ∈ S} → ι) ≃ (κ → ι) :=
    { toFun := fun p => merge S p.1 p.2
      invFun := fun x => (fun r => x r.1, fun r => x r.1)
      left_inv := fun p => by
        rcases p with ⟨u, z⟩
        refine Prod.ext ?_ ?_
        · funext r
          simp [merge, r.2]
        · funext r
          simp [merge, r.2]
      right_inv := fun x => by
        funext r
        by_cases h : r ∈ S <;> simp [merge, h] }
  rw [← Fintype.sum_prod_type']
  exact (e.sum_comp f).symm

theorem partialTrace_smul (S : Finset κ) (t : ℂ) (C : Matrix (κ → ι) (κ → ι) ℂ) :
    partialTrace S (t • C) = t • partialTrace S C := by
  ext u v
  simp [partialTrace, Finset.mul_sum]

theorem frobSq_smul {m n : Type*} [Fintype m] [Fintype n] (t : ℂ) (M : Matrix m n ℂ) :
    frobSq (t • M) = ‖t‖ ^ 2 * frobSq M := by
  simp [frobSq, norm_mul, mul_pow, Finset.mul_sum]

/-- **L2 (homogeneity).** `q(t • C) = |t|² q(C)`. -/
theorem qfun_smul (t : ℂ) (C : Matrix (κ → ι) (κ → ι) ℂ) : qfun (t • C) = ‖t‖ ^ 2 * qfun C := by
  simp only [qfun, partialTrace_smul, frobSq_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

theorem qfun_zero : qfun (0 : Matrix (κ → ι) (κ → ι) ℂ) = 0 := by
  have h := qfun_smul (κ := κ) (ι := ι) 0 0
  simpa using h

end PartialTrace

section Lift

/-- `liftC a b = ∑_r |a_r⟩⟨b_r|`, i.e. `liftC a b x y = ∑_r a (x, r) * conj (b (y, r))`. -/
def liftC {H ρ : Type*} [Fintype ρ] (a b : H × ρ → ℂ) : Matrix H H ℂ :=
  Matrix.of fun x y => ∑ r, a (x, r) * star (b (y, r))

theorem liftC_eq_of {H ρ : Type*} [Fintype ρ] {C : Matrix H H ℂ} {a b : H × ρ → ℂ}
    (h : ∀ x y, C x y = ∑ r, a (x, r) * star (b (y, r))) : C = liftC a b := by
  ext x y
  rw [h x y]
  rfl

/-- The product vector `a ⊗ b` on two replicas. -/
def twoRep {Y : Type*} (a b : Y → ℂ) : Y × Y → ℂ := fun X => a X.1 * b X.2

end Lift

section Swap

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Site digits: take those of `y` on `S` and those of `x` off `S`. -/
def swapSites (S : Finset κ) (x y : κ → ι) : κ → ι := fun r => if r ∈ S then y r else x r

/-- The index map of `F_Q ∏_{i∈S} F_i`: `((x,r),(y,s)) ↦ ((x', s), (y', r))` where `x'`, `y'` are
`x`, `y` with the digits of the sites in `S` exchanged. -/
def swapIdx (S : Finset κ) (X : ((κ → ι) × ρ) × ((κ → ι) × ρ)) :
    ((κ → ι) × ρ) × ((κ → ι) × ρ) :=
  ((swapSites S X.1.1 X.2.1, X.2.2), (swapSites S X.2.1 X.1.1, X.1.2))

variable (ι ρ) in
/-- The permutation operator `F_Q ∏_{i∈S} F_i` on two replicas of `(κ → ι) × ρ`:
`(swapOp ι ρ S *ᵥ v) X = v (swapIdx S X)`. -/
def swapOp (S : Finset κ) :
    Matrix (((κ → ι) × ρ) × ((κ → ι) × ρ)) (((κ → ι) × ρ) × ((κ → ι) × ρ)) ℂ :=
  Matrix.of fun X Y => if Y = swapIdx S X then 1 else 0

theorem swapOp_mulVec (S : Finset κ) (v : ((κ → ι) × ρ) × ((κ → ι) × ρ) → ℂ) :
    swapOp ι ρ S *ᵥ v = fun X => v (swapIdx S X) := by
  funext X
  simp [swapOp, Matrix.mulVec, dotProduct]

theorem swapSites_merge (S : Finset κ) (u u' : {r // r ∉ S} → ι) (z z' : {r // r ∈ S} → ι) :
    swapSites S (merge S u z) (merge S u' z') = merge S u z' := by
  funext r
  by_cases h : r ∈ S <;> simp [swapSites, merge, h]

theorem sum_reorder6 {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] (G : A → B → C → D → E → F → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, G a b c d e f =
      ∑ a, ∑ d, ∑ b, ∑ e, ∑ c, ∑ f, G a b c d e f := by
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, G a b c d e f
      = ∑ b, ∑ d, ∑ c, ∑ e, ∑ f, G a b c d e f :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, ∑ e, ∑ f, G a b c d e f := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ e, ∑ c, ∑ f, G a b c d e f :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **L1 (swap identity).** `‖Tr_S C‖²_F = ⟨a⊗b | F_Q ∏_{i∈S} F_i | a⊗b⟩` for
`C = ∑_r |a_r⟩⟨b_r|`. -/
theorem frobSq_partialTrace_liftC (S : Finset κ) (a b : (κ → ι) × ρ → ℂ) :
    ((frobSq (partialTrace S (liftC a b)) : ℝ) : ℂ) =
      star (twoRep a b) ⬝ᵥ (swapOp ι ρ S *ᵥ twoRep a b) := by
  simp only [frobSq, Complex.ofReal_sum, ofReal_norm_sq, partialTrace, liftC, Matrix.of_apply,
    star_sum, star_mul', star_star, mul_sum_sum]
  rw [swapOp_mulVec]
  simp only [dotProduct, Pi.star_apply, twoRep, swapIdx, Fintype.sum_prod_type, sum_merge S,
    swapSites_merge]
  refine Eq.trans ?_ (sum_reorder6 _).symm
  refine Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [star_mul']
  ring

/-- **L1**, stated for any `C` with `C x y = ∑_r a (x, r) * conj (b (y, r))`. -/
theorem frobSq_partialTrace_eq_swap (S : Finset κ) {C : Matrix (κ → ι) (κ → ι) ℂ}
    {a b : (κ → ι) × ρ → ℂ} (hC : ∀ x y, C x y = ∑ r, a (x, r) * star (b (y, r))) :
    ((frobSq (partialTrace S C) : ℝ) : ℂ) =
      star (twoRep a b) ⬝ᵥ (swapOp ι ρ S *ᵥ twoRep a b) := by
  rw [liftC_eq_of hC]
  exact frobSq_partialTrace_liftC S a b

variable (κ ι ρ) in
/-- The two-replica objective word `W₂ = ∑_S (-1/2)^{|S|} F_Q ∏_{i∈S} F_i`. -/
def objective2 :
    Matrix (((κ → ι) × ρ) × ((κ → ι) × ρ)) (((κ → ι) × ρ) × ((κ → ι) × ρ)) ℂ :=
  ∑ S : Finset κ, ((-1 / 2 : ℂ) ^ S.card) • swapOp ι ρ S

/-- **L1 (objective).** `q(C) = Tr[W₂ · |a⊗b⟩⟨a⊗b|]` for `C = ∑_r |a_r⟩⟨b_r|`. -/
theorem qfun_liftC_eq_trace (a b : (κ → ι) × ρ → ℂ) :
    ((qfun (liftC a b) : ℝ) : ℂ) =
      (objective2 κ ι ρ * vecMulVec (twoRep a b) (star (twoRep a b))).trace := by
  rw [objective2, Finset.sum_mul, Matrix.trace_sum, qfun, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_mul_vecMulVec_star, ← frobSq_partialTrace_liftC,
    smul_eq_mul]
  push_cast; ring

end Swap

end WernerEndpoint

end

#print axioms WernerEndpoint.sum_merge
#print axioms WernerEndpoint.partialTrace_smul
#print axioms WernerEndpoint.frobSq_smul
#print axioms WernerEndpoint.qfun_smul
#print axioms WernerEndpoint.qfun_zero
#print axioms WernerEndpoint.liftC_eq_of
#print axioms WernerEndpoint.swapOp_mulVec
#print axioms WernerEndpoint.frobSq_partialTrace_liftC
#print axioms WernerEndpoint.frobSq_partialTrace_eq_swap
#print axioms WernerEndpoint.qfun_liftC_eq_trace
