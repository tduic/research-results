import WernerEndpoint

open Matrix

noncomputable section

namespace QCheck

/-! Independent definition of q, written from the formula. -/

/-- Frobenius norm squared, written independently. -/
def fro {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

variable {d : ℕ}

/-- C as a 6-index array: `E i0 i1 i2 j0 j1 j2 = ⟨i0 i1 i2| C |j0 j1 j2⟩`. -/
def E (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) (i0 i1 i2 j0 j1 j2 : Fin d) : ℂ :=
  C ![i0, i1, i2] ![j0, j1, j2]

/-- Tr_1 C, indexed by (i1,i2),(j1,j2) -/
def tr1 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => Matrix.trace (Matrix.of fun a b => E C a p.1 p.2 b q.1 q.2)
def tr2 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => Matrix.trace (Matrix.of fun a b => E C p.1 a p.2 q.1 b q.2)
def tr3 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => Matrix.trace (Matrix.of fun a b => E C p.1 p.2 a q.1 q.2 b)
/-- Tr_{12} C, indexed by i2, j2 -/
def tr12 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => Matrix.trace (Matrix.of fun (a b : Fin d × Fin d) => E C a.1 a.2 i b.1 b.2 j)
def tr13 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => Matrix.trace (Matrix.of fun (a b : Fin d × Fin d) => E C a.1 i a.2 b.1 j b.2)
def tr23 (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => Matrix.trace (Matrix.of fun (a b : Fin d × Fin d) => E C i a.1 a.2 j b.1 b.2)

/-- q(C) = Σ_S (−1/2)^{|S|} ‖Tr_S C‖²_F, written out. -/
def myq (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : ℝ :=
  fro C
    - (1/2) * (fro (tr1 C) + fro (tr2 C) + fro (tr3 C))
    + (1/4) * (fro (tr12 C) + fro (tr13 C) + fro (tr23 C))
    - (1/8) * Complex.normSq (Matrix.trace C)


/-! ## Bridge to `WernerEndpoint.qfun` -/
open WernerEndpoint

section helpers
variable {ι : Type} [Fintype ι]

theorem sum_reindex {T : Type} [Fintype T] [DecidableEq T] {n : ℕ} (p : T → Fin n)
    (hp : Function.Bijective p) {M : Type} [AddCommMonoid M] (f : (T → ι) → M) :
    ∑ u, f u = ∑ w : Fin n → ι, f (fun r => w (p r)) := by
  refine Fintype.sum_equiv ((Equiv.ofBijective p hp).arrowCongr (Equiv.refl ι)) _ _ fun u => ?_
  congr 1; funext r; simp [Equiv.arrowCongr_apply, Equiv.ofBijective_symm_apply_apply]

theorem sum_fin_succ {n : ℕ} {M : Type} [AddCommMonoid M] (f : (Fin (n+1) → ι) → M) :
    ∑ w, f w = ∑ a, ∑ w : Fin n → ι, f (Matrix.vecCons a w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _ (fun x => rfl)).symm

theorem sum_fin_zero {M : Type} [AddCommMonoid M] (f : (Fin 0 → ι) → M) :
    ∑ w, f w = f ![] := by
  rw [Fintype.sum_unique]; congr 1
end helpers


abbrev F3 := Fin 3
/-! Explicit position maps for each subset S: remaining sites (in increasing order) and traced sites. -/
def pTe : {r : F3 // r ∉ (∅ : Finset F3)} → Fin 3 := fun r => r.1
def pUe : {r : F3 // r ∈ (∅ : Finset F3)} → Fin 0 := fun r => (Finset.notMem_empty r.1 r.2).elim
def pT0 : {r : F3 // r ∉ ({0} : Finset F3)} → Fin 2 := fun r => if r.1 = 1 then 0 else 1
def pU0 : {r : F3 // r ∈ ({0} : Finset F3)} → Fin 1 := fun _ => 0
def pT1 : {r : F3 // r ∉ ({1} : Finset F3)} → Fin 2 := fun r => if r.1 = 0 then 0 else 1
def pU1 : {r : F3 // r ∈ ({1} : Finset F3)} → Fin 1 := fun _ => 0
def pT2 : {r : F3 // r ∉ ({2} : Finset F3)} → Fin 2 := fun r => if r.1 = 0 then 0 else 1
def pU2 : {r : F3 // r ∈ ({2} : Finset F3)} → Fin 1 := fun _ => 0
def pT01 : {r : F3 // r ∉ ({0, 1} : Finset F3)} → Fin 1 := fun _ => 0
def pU01 : {r : F3 // r ∈ ({0, 1} : Finset F3)} → Fin 2 := fun r => if r.1 = 0 then 0 else 1
def pT02 : {r : F3 // r ∉ ({0, 2} : Finset F3)} → Fin 1 := fun _ => 0
def pU02 : {r : F3 // r ∈ ({0, 2} : Finset F3)} → Fin 2 := fun r => if r.1 = 0 then 0 else 1
def pT12 : {r : F3 // r ∉ ({1, 2} : Finset F3)} → Fin 1 := fun _ => 0
def pU12 : {r : F3 // r ∈ ({1, 2} : Finset F3)} → Fin 2 := fun r => if r.1 = 1 then 0 else 1
def pTa : {r : F3 // r ∉ ({0, 1, 2} : Finset F3)} → Fin 0 := fun r => absurd r.2 (by decide +revert)
def pUa : {r : F3 // r ∈ ({0, 1, 2} : Finset F3)} → Fin 3 := fun r => r.1

theorem hTe : Function.Bijective pTe := by decide
theorem hUe : Function.Bijective pUe := by decide
theorem hT0 : Function.Bijective pT0 := by decide
theorem hU0 : Function.Bijective pU0 := by decide
theorem hT1 : Function.Bijective pT1 := by decide
theorem hU1 : Function.Bijective pU1 := by decide
theorem hT2 : Function.Bijective pT2 := by decide
theorem hU2 : Function.Bijective pU2 := by decide
theorem hT01 : Function.Bijective pT01 := by decide
theorem hU01 : Function.Bijective pU01 := by decide
theorem hT02 : Function.Bijective pT02 := by decide
theorem hU02 : Function.Bijective pU02 := by decide
theorem hT12 : Function.Bijective pT12 := by decide
theorem hU12 : Function.Bijective pU12 := by decide
theorem hTa : Function.Bijective pTa := by decide
theorem hUa : Function.Bijective pUa := by decide

/-! What `merge` produces in each case (the traced indices are shared by row and column). -/
section merges
variable {ι : Type} (a b c : ι)
theorem me : merge (∅ : Finset F3) (fun r => ![a, b, c] (pTe r)) (fun r => (![] : Fin 0 → ι) (pUe r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pTe]
theorem m0 : merge ({0} : Finset F3) (fun r => ![b, c] (pT0 r)) (fun r => ![a] (pU0 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT0, pU0]
theorem m1 : merge ({1} : Finset F3) (fun r => ![a, c] (pT1 r)) (fun r => ![b] (pU1 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT1, pU1]
theorem m2 : merge ({2} : Finset F3) (fun r => ![a, b] (pT2 r)) (fun r => ![c] (pU2 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT2, pU2]
theorem m01 : merge ({0, 1} : Finset F3) (fun r => ![c] (pT01 r)) (fun r => ![a, b] (pU01 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT01, pU01]
theorem m02 : merge ({0, 2} : Finset F3) (fun r => ![b] (pT02 r)) (fun r => ![a, c] (pU02 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT02, pU02]
theorem m12 : merge ({1, 2} : Finset F3) (fun r => ![a] (pT12 r)) (fun r => ![b, c] (pU12 r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pT12, pU12]
theorem ma : merge ({0, 1, 2} : Finset F3) (fun r => (![] : Fin 0 → ι) (pTa r)) (fun r => ![a, b, c] (pUa r)) = ![a, b, c] := by
  funext r; fin_cases r <;> simp [merge, pUa]
end merges

variable (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ)

theorem te : frobSq (partialTrace (∅ : Finset F3) C) = fro C := by
  unfold frobSq partialTrace fro
  simp only [Matrix.of_apply, sum_reindex pTe hTe, sum_reindex pUe hUe,
    sum_fin_succ, sum_fin_zero, me, Complex.normSq_eq_norm_sq]
theorem t0 : frobSq (partialTrace ({0} : Finset F3) C) = fro (tr1 C) := by
  unfold frobSq partialTrace fro tr1 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT0 hT0, sum_reindex pU0 hU0,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m0, Complex.normSq_eq_norm_sq]
theorem t1 : frobSq (partialTrace ({1} : Finset F3) C) = fro (tr2 C) := by
  unfold frobSq partialTrace fro tr2 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT1 hT1, sum_reindex pU1 hU1,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m1, Complex.normSq_eq_norm_sq]
theorem t2 : frobSq (partialTrace ({2} : Finset F3) C) = fro (tr3 C) := by
  unfold frobSq partialTrace fro tr3 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT2 hT2, sum_reindex pU2 hU2,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m2, Complex.normSq_eq_norm_sq]
theorem t01 : frobSq (partialTrace ({0, 1} : Finset F3) C) = fro (tr12 C) := by
  unfold frobSq partialTrace fro tr12 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT01 hT01, sum_reindex pU01 hU01,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m01, Complex.normSq_eq_norm_sq]
theorem t02 : frobSq (partialTrace ({0, 2} : Finset F3) C) = fro (tr13 C) := by
  unfold frobSq partialTrace fro tr13 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT02 hT02, sum_reindex pU02 hU02,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m02, Complex.normSq_eq_norm_sq]
theorem t12 : frobSq (partialTrace ({1, 2} : Finset F3) C) = fro (tr23 C) := by
  unfold frobSq partialTrace fro tr23 E
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pT12 hT12, sum_reindex pU12 hU12,
    sum_fin_succ, sum_fin_zero, Fintype.sum_prod_type, m12, Complex.normSq_eq_norm_sq]
theorem ta : frobSq (partialTrace ({0, 1, 2} : Finset F3) C) = Complex.normSq (Matrix.trace C) := by
  unfold frobSq partialTrace
  simp only [Matrix.of_apply, Matrix.trace, Matrix.diag, sum_reindex pTa hTa, sum_reindex pUa hUa,
    sum_fin_succ, sum_fin_zero, ma, Complex.normSq_eq_norm_sq]

theorem sum_subsets (f : Finset F3 → ℝ) :
    ∑ S, f S = f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} + f {1, 2} + f {0, 1, 2} := by
  rw [show (Finset.univ : Finset (Finset F3)) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **Main check**: Lean's `qfun` equals the independently written q. -/
theorem qfun_eq_myq : WernerEndpoint.qfun C = myq C := by
  unfold qfun
  rw [sum_subsets]
  rw [te, t0, t1, t2, t01, t02, t12, ta]
  have c0 : (∅ : Finset F3).card = 0 := rfl
  have c1 : ({0} : Finset F3).card = 1 := rfl
  have c2 : ({1} : Finset F3).card = 1 := rfl
  have c3 : ({2} : Finset F3).card = 1 := rfl
  have c4 : ({0, 1} : Finset F3).card = 2 := by decide
  have c5 : ({0, 2} : Finset F3).card = 2 := by decide
  have c6 : ({1, 2} : Finset F3).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset F3).card = 3 := by decide
  rw [c0, c1, c2, c3, c4, c5, c6, c7, myq]
  ring

/-- The Lean statement, restated with the independent q. -/
theorem restated (h : ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ WernerEndpoint.qfun C) :
    ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ myq C :=
  fun d C hC => (qfun_eq_myq C) ▸ h d C hC

end QCheck

#print axioms QCheck.qfun_eq_myq
#print axioms QCheck.restated
#check @WernerEndpoint.qfun
#print WernerEndpoint.qfun
#print WernerEndpoint.partialTrace
#print WernerEndpoint.merge
#print WernerEndpoint.frobSq
#print Matrix.rank
