import WernerEndpoint
open Matrix WernerEndpoint
-- d = 1, C = [c]: q = |c|^2 (1 - 3/2 + 3/4 - 1/8) = |c|^2 / 8, computed directly from qfun
example (c : ℂ) : qfun (Matrix.of fun (_ _ : Fin 3 → Fin 1) => c) = ‖c‖ ^ 2 / 8 := by
  unfold qfun frobSq partialTrace
  simp only [Matrix.of_apply, Fintype.sum_unique, Finset.sum_const, Finset.card_univ]
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  simp only [Fintype.card_unique]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [Finset.card_empty, Finset.card_singleton, c4, c5, c6, c7]
  norm_num
  ring
-- statement elaborates: C.rank is Matrix.rank over ℂ
example : ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ),
    C.rank = Module.finrank ℂ (LinearMap.range C.mulVecLin) := fun _ _ => rfl
set_option pp.all false in
#check (∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ WernerEndpoint.qfun C)
