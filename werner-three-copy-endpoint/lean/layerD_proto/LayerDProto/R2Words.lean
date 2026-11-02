import LayerDProto.R2Assembly

/-!
# Layer D, (E′): rows and the objective as `n = 1` parts

A word `w` (index tuple) with coefficient `c` is the part with `k_f = 1`, `X = [[c]]`, `B_l = B_r = [[1]]` and
tables `ρ_f(s) = [[b_f^{cyc(w_f s)}]]` (`b = d` on the sites, `e` on the qubit). `FTP_word`: its functional is
`c · wordNat d e w`, the row functional of `TraceRows.trace_mul_rep`. `objFun_eq`: `8 · objFun` is the
sum of the eight objective words with integer coefficients `(-1)^{|S|} 2^{3-|S|}`
(`TraceRows.trace_objective4_mul_rep`).
-/

open Finset WernerEndpoint

namespace LayerDProto

/-- The 24 `1 × 1` tables `[[b^{cyc(a s)}]]`. -/
def tabOf (b : ℕ) (a : Fin 24) : List (List (List ℤ)) :=
  (List.finRange 24).map fun s => [[((b ^ (cycTab (mulTab a s) : ℕ) : ℕ) : ℤ)]]

/-- The tables of the word `w`. -/
def wordTabs (d e : ℕ) (w : (Fin 3 → Fin 24) × Fin 24) : List (List (List (List ℤ))) :=
  [tabOf d (w.1 0), tabOf d (w.1 1), tabOf d (w.1 2), tabOf e w.2]

theorem tabOf_getD (b : ℕ) (a s : Fin 24) :
    ent ((tabOf b a).getD s []) 0 0 = ((b ^ (cycTab (mulTab a s) : ℕ) : ℕ) : ℤ) := by
  unfold tabOf
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  simp [ent]

theorem FTP_word (P : PartData) (d e : ℕ) (w : (Fin 3 → Fin 24) × Fin 24) (c : ℤ)
    (hks : P.ks = [1, 1, 1, 1]) (hk : P.k = 1) (hX : P.X = [[c]]) (hBl : P.Bl = [[1]]) (hBr : P.Br = [[1]])
    (hr : P.rhos = wordTabs d e w) (ti : (Fin 3 → Fin 24) × Fin 24) :
    FTP P (tupEquiv ti) = c * (wordNat d e w ti : ℤ) := by
  unfold FTP FT FI
  rw [Equiv.symm_apply_apply, hks, hk, hX, hBl, hBr, hr]
  simp only [nth, Fv, K3_nested, Ymat, rhoE, wordTabs, List.getD_cons_zero, List.getD_cons_succ,
    sum_range_one, zero_mul, add_zero, tabOf_getD]
  simp only [ent, List.getD_cons_zero, wordNat, Fin.prod_univ_three]
  push_cast
  ring

/-- The objective's words with integer coefficients: `8 · objFun = ∑_S (-1)^{|S|} 2^{3-|S|} wordNat (objIdx S)`. -/
theorem objFun_eq (d e : ℕ) (t : (Fin 3 → Fin 24) × Fin 24) :
    8 * objFun d e t = ∑ S : Finset (Fin 3),
      (((-1) ^ S.card * 2 ^ (3 - S.card) : ℤ) : ℂ) * (wordNat d e (objIdx S) t : ℂ) := by
  unfold objFun
  rw [mul_sum]
  refine sum_congr rfl fun S _ => ?_
  have h3 : S.card ≤ 3 := by simpa using S.card_le_univ
  rw [← mul_assoc]
  congr 1
  push_cast
  interval_cases h : S.card <;> norm_num

end LayerDProto

#print axioms LayerDProto.FTP_word
#print axioms LayerDProto.objFun_eq
