import LayerDT0.PDCheck
import LayerDProto.PDSound
import WernerEndpoint.L9_Pairing

/-!
# Layer D (t = 0): positive definiteness of the block multipliers (obligation 5)

`BlockPD.X DEN b = X0 / 2^s + diag(Δ) / DEN` is the verifier's `X_b`. `BlockPD.X_posDef`: if the
kernel check `pdChk DEN b` passes, `X_b ≻ 0` (via `posDef_shift_of_checkPDdd` and L9's
`certificate_posDef`). `posDef_of_all`: one passing `List.all` over a list of blocks gives every
listed block.
-/

open Matrix

namespace LayerDT0

open WernerEndpoint LayerDProto

/-- The correction of diagonal entry `i` (`0` if none). -/
def deltaAt (Δ : List (ℕ × ℤ)) (i : ℕ) : ℤ := (Δ.lookup i).getD 0

/-- **The block multiplier** `X0 / 2^s + diag(Δ) / DEN`. -/
noncomputable def BlockPD.X (DEN : ℕ) (b : BlockPD) : Matrix (Fin b.k) (Fin b.k) ℝ :=
  ((2 : ℝ) ^ (b.s : ℤ))⁻¹ • (toMat b.k b.X0).map (Int.cast : ℤ → ℝ) +
    diagonal fun i : Fin b.k => (deltaAt b.Δ i : ℝ) / DEN

theorem lookup_mem : ∀ (Δ : List (ℕ × ℤ)) (i : ℕ) (v : ℤ), Δ.lookup i = some v → (i, v) ∈ Δ
  | [], _, _, h => by simp at h
  | (a, w) :: l, i, v, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hia
      simp only [Option.some.injEq] at h
      have : i = a := by simpa using hia
      subst this h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem l i v h)

theorem BlockPD.X_posDef {DEN : ℕ} {b : BlockPD} (h : pdChk DEN b = true) : (b.X DEN).PosDef := by
  simp only [pdChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpd, hme⟩, hΔ⟩ := h
  have hA := posDef_shift_of_checkPDdd (X0 := b.X0) b.s b.mn b.me hme hpd
  refine certificate_posDef (toMat b.k b.X0) (b.s : ℤ) DEN (fun i => deltaAt b.Δ i) _ hA fun i => ?_
  rw [deltaOK, List.all_eq_true] at hΔ
  have hμ : (0 : ℝ) ≤ (b.mn : ℝ) / 2 ^ b.me := by positivity
  show |((deltaAt b.Δ i : ℤ) : ℝ)| / DEN ≤ _
  rcases hl : b.Δ.lookup (i : ℕ) with _ | v
  · have hd : deltaAt b.Δ i = 0 := by simp [deltaAt, hl]
    rw [hd]; simpa using hμ
  · have hd : deltaAt b.Δ i = v := by simp [deltaAt, hl]
    rw [hd]
    have hc := hΔ _ (lookup_mem _ _ _ hl)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases Nat.eq_zero_or_pos DEN with h0 | h0
    · simp [h0, hμ]
    · have h2 : (0 : ℝ) < 2 ^ b.me := by positivity
      have hD : (0 : ℝ) < DEN := by exact_mod_cast h0
      rw [div_le_div_iff₀ hD h2]
      have hcast : ((v.natAbs * 2 ^ b.me : ℕ) : ℝ) ≤ ((b.mn * DEN : ℕ) : ℝ) := by exact_mod_cast hc.2
      push_cast at hcast
      rw [Int.cast_natAbs] at hcast
      simpa [Int.cast_abs] using hcast

theorem pdChk_getD {DEN : ℕ} {l : List BlockPD} (h : l.all (pdChk DEN) = true) {j : ℕ}
    (hj : j < l.length) : pdChk DEN (l.getD j default) = true := by
  rw [List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact h _ (List.getElem_mem hj)

end LayerDT0

#print axioms LayerDT0.BlockPD.X_posDef
