import Trifference.N10M30
import Trifference.N11M36
import Trifference.N12M48
import Trifference.N16M108
import Trifference.N17M109

/-! Independent restatement, written separately by a reviewer:
`IsTrifferent` is proved equivalent to `Trifference.Trifferent`, each bound is restated as `TLowerBound n k`,
and `not_trifferent_example` shows the definition rejects a non-trifferent code (it is not vacuous). -/

/-- every 3 pairwise-distinct codewords have a coordinate where all three are pairwise distinct -/
def IsTrifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a ≠ b → a ≠ c → b ≠ c →
    ∃ i : Fin n, a i ≠ b i ∧ a i ≠ c i ∧ b i ≠ c i

theorem isTrifferent_iff {n : ℕ} (C : Finset (Fin n → Fin 3)) :
    IsTrifferent C ↔ Trifference.Trifferent C := by
  constructor
  · intro h x hx y hy z hz hxy hyz hxz
    obtain ⟨i, h1, h2, h3⟩ := h x hx y hy z hz hxy hxz hyz
    exact ⟨i, h1, h3, h2⟩
  · intro h a ha b hb c hc hab hac hbc
    obtain ⟨i, h1, h2, h3⟩ := h a ha b hb c hc hab hbc hac
    exact ⟨i, h1, h3, h2⟩

/-- T(n) ≥ k, stated independently -/
def TLowerBound (n k : ℕ) : Prop := ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ C.card ≥ k

theorem of_prod {n k : ℕ} (h : ∃ C : Finset (Fin n → Fin 3), Trifference.Trifferent C ∧ k ≤ C.card) :
    TLowerBound n k := by
  obtain ⟨C, h1, h2⟩ := h; exact ⟨C, (isTrifferent_iff C).2 h1, h2⟩

theorem T10_ge_30 : TLowerBound 10 30 := of_prod Trifference.T_ge_N10M30
theorem T11_ge_36 : TLowerBound 11 36 := of_prod Trifference.T_ge_N11M36
theorem T12_ge_48 : TLowerBound 12 48 := of_prod Trifference.T_ge_N12M48
theorem T16_ge_108 : TLowerBound 16 108 := of_prod Trifference.T_ge_N16M108
theorem T17_ge_109 : TLowerBound 17 109 := of_prod Trifference.T_ge_N17M109

-- sanity: the definition is not vacuous; a non-trifferent 3-word code is rejected
theorem not_trifferent_example : ¬ IsTrifferent ({fun _ => 0, fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 1} : Finset (Fin 2 → Fin 3)) := by
  intro h
  have := h (fun _ => 0) (by simp) (fun i => if i = 0 then 1 else 0) (by simp)
    (fun i => if i = 0 then 0 else 1) (by simp)
    (by intro e; have := congrFun e 0; simp at this)
    (by intro e; have := congrFun e 1; simp at this)
    (by intro e; have := congrFun e 0; simp at this)
  obtain ⟨i, h1, h2, h3⟩ := this
  revert h1 h2 h3; revert i; decide

#print axioms T10_ge_30
#print axioms T11_ge_36
#print axioms T12_ge_48
#print axioms T16_ge_108
#print axioms T17_ge_109
#print axioms not_trifferent_example
