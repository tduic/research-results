import LayerDT0.Basic
import WernerEndpoint.LayerC_Walled

/-!
# Layer D (t = 0): the walled-Brauer tables (`TabAt` for every `d ≥ 1`)

A table is given by two `24 × 24` natural-number lists `S`, `L` (the verifier's literal table:
`Γ_T(P_a) Γ_T(P_b) = d^{L a b} Γ_T(P_{S a b})`), read through `permIdx` (`tabOf`).

* `tabAt_of_cert`: for a cut with a kernel-checked layer-C certificate table (`{3}` and `{2, 3}`:
  `chkT3`, `chkT23`), it suffices that `S`, `L` agree with the certificates' `(u, c)`.
* `tabAt_relabel`: a relabelling `π` of the replicas carrying the slot maps of `T` to those of
  `T'` (index map `ci`, a bijection) carries a valid table of `T` to one of `T'`.
* `tabAt_empty`: for `T = ∅`, `S a b = a·b` and `L = 0`.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint

def n2 (l : List (List ℕ)) (i j : ℕ) : ℕ := (l.getD i []).getD j 0

/-- The table's product index, as `Fin 24`. -/
def tS (S : List (List ℕ)) (i j : ℕ) : Fin 24 := fin24 (n2 S i j)

/-- **The table of a block** from the verifier's `(S, L)` lists. -/
def tabOf (S L : List (List ℕ)) : P4 → P4 → P4 × ℕ :=
  fun p q => (permTab (tS S (permIdx p) (permIdx q)), n2 L (permIdx p) (permIdx q))

theorem tabOf_permTab (S L : List (List ℕ)) (i j : Fin 24) :
    tabOf S L (permTab i) (permTab j) = (permTab (tS S i j), n2 L i j) := by
  simp only [tabOf, permIdx_permTab]

/-- Agreement of `(S, L)` with a packed layer-C certificate table. -/
def tabCertRow (rows : Fin 24 → ℕ) (S L : List (List ℕ)) (i : ℕ) : Bool :=
  (List.range 24).all fun j =>
    tS S i j == (certOf rows (fin24 i) (fin24 j)).u && n2 L i j == (certOf rows (fin24 i) (fin24 j)).c

theorem tabAt_of_cert {T : Finset (Fin 4)} {rows muRow : Fin 24 → ℕ} {S L : List (List ℕ)}
    (hmu : ∀ i q, muC muRow i q = muT T i q) (hchk : ∀ i j, chkB rows muRow i j = true)
    (h : ∀ i : Fin 24, tabCertRow rows S L i = true) {d : ℕ} (hd : 1 ≤ d) : TabAt T d (tabOf S L) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro p q
  obtain ⟨i, rfl⟩ := permTab_surj p
  obtain ⟨j, rfl⟩ := permTab_surj q
  have hij := all_range (h i) j.isLt
  simp only [Bool.and_eq_true, beq_iff_eq, fin24_val] at hij
  rw [tabOf_permTab, hij.1, hij.2]
  simp only [Osite]
  rw [ptrans_sP_eq_br, ptrans_sP_eq_br, ptrans_sP_eq_br]
  have := br_mul_br (α := Fin d) (chkB_sound hmu (hchk i j))
  simpa [Fintype.card_fin] using this

theorem tabAt_empty {S L : List (List ℕ)}
    (h : ∀ i j : Fin 24, (∀ x, permFun (tS S i j) x = permFun i (permFun j x)) ∧ n2 L i j = 0)
    (d : ℕ) : TabAt ∅ d (tabOf S L) := by
  intro p q
  obtain ⟨i, rfl⟩ := permTab_surj p
  obtain ⟨j, rfl⟩ := permTab_surj q
  have e : permTab (tS S i j) = permTab i * permTab j := Equiv.ext fun x => (h i j).1 x
  rw [tabOf_permTab, e, (h i j).2]
  simp only [Osite, ptrans_empty, sP_mul, pow_zero, Nat.cast_one, one_smul]

/-- Relabelling the replicas carries a table of `T` to a table of `T'`. -/
theorem tabAt_relabel (π : Equiv.Perm (Fin 4)) {T T' : Finset (Fin 4)} (ci : Fin 24 → Fin 24)
    (hrel : ∀ i : Fin 24, ∀ q, Equiv.sumCongr π π (muT T i ((Equiv.sumCongr π π).symm q)) =
      muT T' (ci i) q)
    (hsurj : ∀ i' : Fin 24, ∃ i, ci i = i')
    {S L S' L' : List (List ℕ)}
    (hct : ∀ i j : Fin 24, tS S' (ci i) (ci j) = ci (tS S i j) ∧ n2 L' (ci i) (ci j) = n2 L i j)
    {d : ℕ} (htab : TabAt T d (tabOf S L)) : TabAt T' d (tabOf S' L') := by
  have key : ∀ i : Fin 24, rearr (Equiv.sumCongr π π) (Osite T (Fin d) (permTab i)) =
      Osite T' (Fin d) (permTab (ci i)) := by
    intro i
    simp only [Osite]
    rw [ptrans_sP_eq_br, ptrans_sP_eq_br, rearr_br]
    exact br_congr (hrel i)
  intro p q
  obtain ⟨i', rfl⟩ := permTab_surj p
  obtain ⟨j', rfl⟩ := permTab_surj q
  obtain ⟨i, rfl⟩ := hsurj i'
  obtain ⟨j, rfl⟩ := hsurj j'
  have h0 := htab (permTab i) (permTab j)
  rw [tabOf_permTab] at h0
  rw [tabOf_permTab, (hct i j).1, (hct i j).2, ← key, ← key, ← key, ← rearr_sumCongr_mul, h0,
    rearr_smul]

end LayerDT0

#print axioms LayerDT0.tabAt_of_cert
#print axioms LayerDT0.tabAt_empty
#print axioms LayerDT0.tabAt_relabel
