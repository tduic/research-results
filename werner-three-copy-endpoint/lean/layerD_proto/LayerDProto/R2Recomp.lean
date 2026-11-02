import LayerDProto.R2Reduced
import LayerDProto.R2RecompKernel

/-!
# Layer D, (E′): soundness of the full-rank re-presentation of a part

* `Ymat_eq_of_yEqOK`: if `yEqOK w k X Bl Br k' X' Bl' Br'` holds, then `Ymat k X Bl Br = Ymat k' X' Bl' Br'`
  (as functions `ℕ → ℕ → ℤ`): the packed rows are equal, both rows' digits are bounded by `D` with
  `4 D < 2^w`, so their balanced digits are equal (`digitsAt_spec`); outside the rows/columns both are `0`.
* `FTP_ycongr`: if `ycoreOK w P P'`, then `P.fac = P'.fac` and `FTP P = FTP P'`.

Nothing about the re-presentation (ranks, bases, how it was found) is used: only the checked equality.
-/

open Finset

namespace LayerDProto

theorem all_len_of_all {Bl : List (List ℤ)} {k : ℕ} (h : Bl.all (·.length == k) = true) :
    ∀ r ∈ Bl, r.length = k := by
  intro r hr
  simpa using List.all_eq_true.mp h r hr

theorem ent_eq_zero_of_ge (L : List (List ℤ)) (i j : ℕ) (hi : L.length ≤ i) : ent L i j = 0 := by
  simp [ent, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem Ymat_row_ge (k : ℕ) (X Bl Br : List (List ℤ)) (i j : ℕ) (hi : Bl.length ≤ i) :
    Ymat k X Bl Br i j = 0 := by
  unfold Ymat
  simp [ent_eq_zero_of_ge Bl i _ hi]

theorem Ymat_col_ge (k : ℕ) (X Bl Br : List (List ℤ)) (i j : ℕ) (hj : Br.length ≤ j) :
    Ymat k X Bl Br i j = 0 := by
  unfold Ymat
  simp [ent_eq_zero_of_ge Br j _ hj]

/-- **The checked re-presentation has the same `Y`.** -/
theorem Ymat_eq_of_yEqOK (w k : ℕ) (X Bl Br : List (List ℤ)) (k' : ℕ) (X' Bl' Br' : List (List ℤ))
    (h : yEqOK w k X Bl Br k' X' Bl' Br' = true) : Ymat k X Bl Br = Ymat k' X' Bl' Br' := by
  simp only [yEqOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hw⟩, hX⟩, hBl⟩, hBr⟩, hX'⟩, hBl'⟩, hBr'⟩, hb⟩, hb'⟩, hy⟩ := h
  obtain ⟨hXl, hXr⟩ := isRect_spec _ _ X hX
  obtain ⟨hXl', hXr'⟩ := isRect_spec _ _ X' hX'
  have hBl1 := all_len_of_all hBl
  have hBr1 := all_len_of_all hBr
  have hBl1' := all_len_of_all hBl'
  have hBr1' := all_len_of_all hBr'
  obtain ⟨_, hs⟩ := yRows_spec k w Br.length X Bl Br hXl hXr rfl hBr1
  obtain ⟨_, hs'⟩ := yRows_spec k' w Br.length X' Bl' Br' hXl' hXr' hr hBr1'
  -- one digit bound for both sides
  obtain ⟨D, hD1, hD2, hD4⟩ : ∃ D : ℕ, rowSumMax Bl * entMax X * rowSumMax Br ≤ D ∧
      rowSumMax Bl' * entMax X' * rowSumMax Br' ≤ D ∧ 4 * D < 2 ^ w := by
    rcases le_total (rowSumMax Bl * entMax X * rowSumMax Br) (rowSumMax Bl' * entMax X' * rowSumMax Br')
      with hab | hab
    · exact ⟨_, hab, le_refl _, hb'⟩
    · exact ⟨_, le_refl _, hab, hb⟩
  funext i j
  by_cases hi : i < Bl.length
  swap
  · rw [Ymat_row_ge _ _ _ _ i j (by omega), Ymat_row_ge _ _ _ _ i j (by omega)]
  by_cases hj : j < Br.length
  swap
  · rw [Ymat_col_ge _ _ _ _ i j (by omega), Ymat_col_ge _ _ _ _ i j (by omega)]
  have hrow := congrArg (fun L => L.getD i 0) hy
  simp only at hrow
  rw [hs i hBl1, hs' i hBl1'] at hrow
  have hpos : ∀ j ∈ List.range Br.length, j < Br.length := fun j hj => List.mem_range.mp hj
  have hd1 := digitsAt_spec w Br.length hw (fun j => Ymat k X Bl Br i j) D
    (fun j _ => (Ymat_bound k X Bl Br hBl1 hBr1 i j).trans (by exact_mod_cast hD1)) hD4 _ hpos
  have hd2 := digitsAt_spec w Br.length hw (fun j => Ymat k' X' Bl' Br' i j) D
    (fun j _ => (Ymat_bound k' X' Bl' Br' hBl1' hBr1' i j).trans (by exact_mod_cast hD2)) hD4 _ hpos
  have hm : (List.range Br.length).map (fun j => Ymat k X Bl Br i j) =
      (List.range Br.length).map (fun j => Ymat k' X' Bl' Br' i j) := by
    rw [← hd1, ← hd2]
    unfold Ymat
    rw [hrow]
  exact List.map_inj_left.mp hm j (List.mem_range.mpr hj)

/-- **A checked re-presentation has the same functional.** -/
theorem FTP_ycongr (w : ℕ) (P P' : PartData) (h : ycoreOK w P P' = true) :
    P.fac = P'.fac ∧ FTP P = FTP P' := by
  simp only [ycoreOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hks, hfac⟩, hrh⟩, hy⟩ := h
  refine ⟨hfac, funext fun t => ?_⟩
  unfold FTP
  rw [hks, hrh, Ymat_eq_of_yEqOK _ _ _ _ _ _ _ _ _ hy]

/-! ### Controls (kernel): `B_u = [b 0]`, `B_v = [0 b]` with `b = (1, 2, 0)ᵀ` (rank 1 of k = 2, as in a
coupled block) and its rank-1 re-presentation `L = R = b`, `Z = [X_uv]`. -/

/-- positive: `Y = b X₀₁ bᵀ` is reproduced. -/
example : yEqOK 12 2 [[5, 3], [3, 7]] [[1, 0], [2, 0], [0, 0]] [[0, 1], [0, 2], [0, 0]]
    1 [[3]] [[1], [2], [0]] [[1], [2], [0]] = true := by decide +kernel

/-- negative: the wrong block (`X₀₀ = 5` instead of `X₀₁ = 3`) is rejected. -/
example : yEqOK 12 2 [[5, 3], [3, 7]] [[1, 0], [2, 0], [0, 0]] [[0, 1], [0, 2], [0, 0]]
    1 [[5]] [[1], [2], [0]] [[1], [2], [0]] = false := by decide +kernel

/-- negative: a digit width too small for the bound (`4 · 2 · 7 · 2 = 112 ≥ 2^6`) is rejected even with equal `Y`. -/
example : yEqOK 6 2 [[5, 3], [3, 7]] [[1, 0], [2, 0], [0, 0]] [[0, 1], [0, 2], [0, 0]]
    1 [[3]] [[1], [2], [0]] [[1], [2], [0]] = false := by decide +kernel

end LayerDProto

#print axioms LayerDProto.Ymat_eq_of_yEqOK
#print axioms LayerDProto.FTP_ycongr
