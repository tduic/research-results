import LayerDT0.IdentityBlock

/-!
# Layer D (t = 0): the bookkeeping `hdec` of the identity

`identity_of_decomp` (`IdentityAsm.lean`) needs, for one nonzero scale `S`,
`S · (rhs μ − lhs μ) = ∑_f ∑_t μ_f(t) D_f(t)` with `D_f = famD (Ps f)`. This file builds the part lists
`Ps f` as Lean functions of the certificate data (no literal is compared) and proves that equation for
every `μ`:

* **Rows and objective** (`IdentityUnit.lean`): `mRowVal_uterms`, `mObj_uterms` write them as integer
  combinations of `1 × 1` unit parts (`unitPart`).
* **Blocks** (`blockParts`, `block_dec`): `X_b = X0/2^s + diag(Δ)/DEN`, so `xint = X0 · DEN + δ Δ · 2^s` is
  `c · X_b` with `c = 2^s · DEN`; the bridge (`pair_word`, `pair_c3`, `pair_c23`) with `fac = S / c`
  (`2 S / c` for the `22` part of a coupled block). `Xᵀ = X` comes from `X_posDef`.
* **Regrouping** (`regroup`): a list of family-tagged parts sums to `∑_f ∑_t μ_f(t) famD (psOf L f) t`.
* **`hdec_of_data`**: the equation for `allParts`, i.e. the objective's parts (sign `−`), the blocks'
  parts in `blocks.jsonl` order and the rows' parts in row order; **`identity_of_parts`**: the hypothesis
  `hid` of `endpoint_of_data` from `FamZero f (psOf allParts f)` for the three families.
* `famZero_congr` (`Totals.lean`): `famD` only reads `fac` and the fields `FTP` reads, so a generated part
  list that agrees with `psOf allParts f` on those fields (`PartData.core`) has the same `FamZero`.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint LayerDProto

/-! ### Rows and objective -/

/-- A row's tagged parts, with `fac = coef · lamNum_r · (S / lamDen)`. -/
def rowParts (S : ℕ) (num : List ℤ) (den : ℕ) (r : ℕ) (c : RowCode) : List (Fam × PartData) :=
  c.uterms.map fun u => (u.f, unitPart (u.coef * num.getD r 0 * ((S / den : ℕ) : ℤ)) u.j u.a)

theorem unitPart_fac (fac : ℤ) (j : Fin 3 → Fin 24) (a : Fin 24) : (unitPart fac j a).fac = fac := rfl

theorem tval_unit (μ : Fam → Tup (Fin 3) → ℝ) (fac : ℤ) (u : UTerm) :
    tval μ (u.f, unitPart fac u.j u.a) = (fac : ℝ) * u.val μ := by
  have e : FTP (unitPart fac u.j u.a) = FTP (unitPart 0 u.j u.a) := rfl
  rw [tval_eq, unitPart_fac, e, UTerm.val]

theorem row_dec {den : ℕ} (hden : 0 < den) (S : ℕ) (hS : S % den = 0) (num : List ℤ) (r : ℕ) (c : RowCode)
    (μ : Fam → Tup (Fin 3) → ℝ) :
    (S : ℝ) * (lamOf num den r * mRowVal 2 c.row μ) = ((rowParts S num den r c).map (tval μ)).sum := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have key : (S : ℝ) * lamOf num den r = (num.getD r 0 : ℝ) * ((S / den : ℕ) : ℝ) := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hS)
    have h' : (S : ℝ) = ((S / den : ℕ) : ℝ) * den := by exact_mod_cast this.symm
    rw [lamOf, h']
    field_simp
  rw [← mul_assoc, key, mRowVal_uterms, rowParts, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun u _ => ?_
  rw [Function.comp_apply, tval_unit, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  generalize u.val μ = v
  ring

/-- The objective's tagged parts, with sign `−` and `fac = −coef · (S / 8)`. -/
def objParts (S : ℕ) : List (Fam × PartData) :=
  objUTerms.map fun u => (u.f, unitPart (-(u.coef * ((S / 8 : ℕ) : ℤ))) u.j u.a)

theorem obj_dec (S : ℕ) (hS : S % 8 = 0) (μ : Fam → Tup (Fin 3) → ℝ) :
    -((S : ℝ) * mObj 2 μ) = ((objParts S).map (tval μ)).sum := by
  have hS1 : (S : ℝ) = (-((S / 8 : ℕ) : ℝ)) * (-8) := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hS)
    have h' : (S : ℝ) = ((S / 8 : ℕ) : ℝ) * 8 := by exact_mod_cast this.symm
    rw [h']; ring
  rw [hS1, mul_assoc, show -(-((S / 8 : ℕ) : ℝ) * (-8 * mObj 2 μ)) = -((S / 8 : ℕ) : ℝ) * (8 * mObj 2 μ) by ring,
    mObj_uterms, objParts, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun u _ => ?_
  rw [Function.comp_apply, tval_unit, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  generalize u.val μ = v
  ring

/-! ### The whole identity -/

/-- The scale checks: `0 < DEN`, `0 < lamDen`, `2^{s_b} DEN ∣ S` for every block, `lamDen ∣ S`, `8 ∣ S`. -/
def scaleOK (DEN den S nb : ℕ) (pds : List BlockPD) : Bool :=
  decide (0 < DEN) && decide (0 < den) && S % den == 0 && S % 8 == 0 &&
    pds.all fun pd => S % (2 ^ pd.s * DEN) == 0

/-- All tagged parts: objective, then blocks (in order), then rows (in order). -/
def allParts (cuts : ℕ → CutData) (DEN S nb : ℕ) (bcs : List BCode) (pds : List BlockPD) (nr : ℕ)
    (codes : List RowCode) (num : List ℤ) (den : ℕ) : List (Fam × PartData) :=
  objParts S ++ ((List.range nb).flatMap fun j => blockParts cuts DEN S (bcs.getD j default) (pds.getD j default)) ++
    ((List.range nr).flatMap fun r => rowParts S num den r (rowAt codes r))

/-- **`hdec`** for the explicit data. -/
theorem hdec_of_data (cuts : ℕ → CutData) (DEN S nb : ℕ) (bcs : List BCode) (pds : List BlockPD)
    (hpd : pds.all (pdChk DEN) = true) (hlen : nb ≤ pds.length) (nr : ℕ) (codes : List RowCode)
    (num : List ℤ) (den : ℕ) (hsc : scaleOK DEN den S nb pds = true) (μ : Fam → Tup (Fin 3) → ℝ) :
    (S : ℝ) * ((∑ j : Fin nb, ∑ i, ∑ i', (pds.getD j default).X DEN i i' *
          ((bcs.getD j default).toSpec cuts (pds.getD j default).k).L μ i i' +
        ∑ r : Fin nr, lamOf num den r * mRowVal 2 (rowAt codes r).row μ) - mObj 2 μ) =
      ∑ f : Fam, ∑ t, μ f t * (famD (psOf (allParts cuts DEN S nb bcs pds nr codes num den) f) t : ℝ) := by
  simp only [scaleOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hsc
  obtain ⟨⟨⟨⟨hD, hden⟩, hSd⟩, hS8⟩, hSb0⟩ := hsc
  have hSb : ∀ j : Fin nb, S % (2 ^ (pds.getD j default).s * DEN) = 0 := fun j => by
    have hj := lt_of_lt_of_le j.isLt hlen
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hSb0 _ (List.getElem_mem hj)
  rw [← regroup, allParts, List.map_append, List.map_append, List.sum_append, List.sum_append,
    ← obj_dec S hS8, sum_flatMap_map, sum_flatMap_map, listSum_range, listSum_range]
  have hb : ∀ j : Fin nb, ((blockParts cuts DEN S (bcs.getD j default) (pds.getD j default)).map (tval μ)).sum =
      (S : ℝ) * ∑ i, ∑ i', (pds.getD j default).X DEN i i' *
        ((bcs.getD j default).toSpec cuts (pds.getD j default).k).L μ i i' := fun j =>
    (block_dec cuts hD S _ _ (pdChk_getD hpd (lt_of_lt_of_le j.isLt hlen)) (hSb j) μ).symm
  have hr : ∀ r : Fin nr, ((rowParts S num den r (rowAt codes r)).map (tval μ)).sum =
      (S : ℝ) * (lamOf num den r * mRowVal 2 (rowAt codes r).row μ) := fun r =>
    (row_dec hden S hSd num r _ μ).symm
  simp only [hb, hr, ← Finset.mul_sum]
  ring

/-- **The identity from the three family zeros.** -/
theorem identity_of_parts (cuts : ℕ → CutData) (DEN S nb : ℕ) (bcs : List BCode) (pds : List BlockPD)
    (hpd : pds.all (pdChk DEN) = true) (hlen : nb ≤ pds.length) (nr : ℕ) (codes : List RowCode)
    (num : List ℤ) (den : ℕ) (hsc : scaleOK DEN den S nb pds = true) (hS : 0 < S)
    (hz : ∀ f, FamZero f (psOf (allParts cuts DEN S nb bcs pds nr codes num den) f))
    (μ : Fam → Tup (Fin 3) → ℝ) (hμ : OrbInv (Fin 3) μ) :
    mObj 2 μ = ∑ j : Fin nb, ∑ i, ∑ i', (pds.getD j default).X DEN i i' *
          ((bcs.getD j default).toSpec cuts (pds.getD j default).k).L μ i i' +
        ∑ r : Fin nr, lamOf num den r * mRowVal 2 (rowAt codes r).row μ :=
  identity_of_decomp (mObj 2) (fun μ => ∑ j : Fin nb, ∑ i, ∑ i', (pds.getD j default).X DEN i i' *
          ((bcs.getD j default).toSpec cuts (pds.getD j default).k).L μ i i' +
        ∑ r : Fin nr, lamOf num den r * mRowVal 2 (rowAt codes r).row μ) S
    (by exact_mod_cast hS.ne') _ (hdec_of_data cuts DEN S nb bcs pds hpd hlen nr codes num den hsc) hz μ hμ

end LayerDT0

#print axioms LayerDT0.hdec_of_data
#print axioms LayerDT0.identity_of_parts
