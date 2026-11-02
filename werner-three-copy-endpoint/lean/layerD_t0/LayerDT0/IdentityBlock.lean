import LayerDT0.IdentityUnit
import LayerDT0.XInt

/-!
# Layer D (t = 0): family-tagged parts and the blocks (second part of the `hdec` bookkeeping)

* `tval`, `psOf`, **`regroup`**: a list of family-tagged parts sums to `∑_f ∑_t μ_f(t) famD (psOf L f) t`.
* `famD_append`. (`FamZero` only reads the parts' cores: `famZero_congr` in `Totals.lean`.)
* **`block_dec`**: `X_b = X0/2^s + diag(Δ)/DEN`, so `xint = X0 · DEN + δ Δ · 2^s` is `c · X_b` with
  `c = 2^s · DEN`; the bridge (`pair_word`, `pair_c3`, `pair_c23`) with `fac = S / c` (`2 S / c` for the
  `22` part of a coupled block) gives `S ⟨X_b, L_b(μ)⟩ = ∑` of the block's tagged parts. `Xᵀ = X` comes
  from `X_posDef`.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint LayerDProto

/-! ### Family-tagged part lists -/

/-- The pairing of a tagged part with `μ`: `∑_t μ_f(t) fac FTP(t)`. -/
noncomputable def tval (μ : Fam → Tup (Fin 3) → ℝ) (x : Fam × PartData) : ℝ :=
  ∑ t, μ x.1 t * ((x.2.fac * FTP x.2 t : ℤ) : ℝ)

/-- The parts of family `f`, in list order. -/
def psOf (L : List (Fam × PartData)) (f : Fam) : List PartData := (L.filter fun x => decide (x.1 = f)).map Prod.snd

theorem famD_nil (t : Tup (Fin 3)) : famD [] t = 0 := rfl

theorem famD_cons (P : PartData) (Ps : List PartData) (t : Tup (Fin 3)) :
    famD (P :: Ps) t = P.fac * FTP P t + famD Ps t := by
  simp [famD]

/-- **Regrouping by family.** -/
theorem regroup (L : List (Fam × PartData)) (μ : Fam → Tup (Fin 3) → ℝ) :
    (L.map (tval μ)).sum = ∑ f : Fam, ∑ t, μ f t * (famD (psOf L f) t : ℝ) := by
  induction L with
  | nil => simp [psOf, famD_nil]
  | cons x L ih =>
    have hp : ∀ f, psOf (x :: L) f = if x.1 = f then x.2 :: psOf L f else psOf L f := by
      intro f
      by_cases h : x.1 = f <;> simp [psOf, h]
    have hd : ∀ f t, μ f t * (famD (psOf (x :: L) f) t : ℝ) =
        (if x.1 = f then μ x.1 t * ((x.2.fac * FTP x.2 t : ℤ) : ℝ) else 0) + μ f t * (famD (psOf L f) t : ℝ) := by
      intro f t
      rw [hp]
      split_ifs with h
      · subst h
        rw [famD_cons]
        push_cast
        ring
      · simp
    rw [List.map_cons, List.sum_cons, ih]
    simp_rw [hd, Finset.sum_add_distrib]
    rw [add_left_inj]
    rw [Finset.sum_comm, tval]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp

theorem famD_append (Ps Qs : List PartData) (t : Tup (Fin 3)) : famD (Ps ++ Qs) t = famD Ps t + famD Qs t := by
  simp [famD, List.map_append, List.sum_append]

/-! ### Blocks -/

theorem xdelta_eq (Δ : List (ℕ × ℤ)) (i : ℕ) : xdelta Δ i = deltaAt Δ i := rfl

theorem xdiag_eq (Δ : List (ℕ × ℤ)) (i s : ℕ) : xdelta Δ i * (2 : ℤ) ^ s = deltaAt Δ i * 2 ^ s := by
  rw [xdelta_eq]

theorem headD_eq_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by cases l <;> rfl

theorem tail_getD {α : Type} (l : List α) (d : α) (j : ℕ) : l.tail.getD j d = l.getD (j + 1) d := by
  cases l <;> simp

theorem xrowF_getD (DEN : ℕ) (dv : ℤ) (p : ℕ) :
    ∀ (n q : ℕ) (r : List ℤ) (j : ℕ), j < n →
      (xrowF DEN dv p q r n).getD j 0 = r.getD j 0 * DEN + if p = q + j then dv else 0
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, r, 0, _ => by rw [xrowF, List.getD_cons_zero, headD_eq_getD]; simp
  | n + 1, q, r, j + 1, h => by
    rw [xrowF, List.getD_cons_succ, xrowF_getD DEN dv p n (q + 1) r.tail j (by omega), tail_getD,
      show q + 1 + j = q + (j + 1) by omega]

theorem xrowsF_getD (DEN : ℕ) (pd : BlockPD) :
    ∀ (n p : ℕ) (X : List (List ℤ)) (i : ℕ), i < n →
      (xrowsF DEN pd p X n).getD i [] = xrowF DEN (xdelta pd.Δ (p + i) * 2 ^ pd.s) (p + i) 0 (X.getD i []) pd.k
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, p, X, 0, _ => by rw [xrowsF, List.getD_cons_zero, headD_eq_getD]; simp
  | n + 1, p, X, i + 1, h => by
    rw [xrowsF, List.getD_cons_succ, xrowsF_getD DEN pd n (p + 1) X.tail i (by omega), tail_getD,
      show p + 1 + i = p + (i + 1) by omega]

theorem ent_xint (DEN : ℕ) (pd : BlockPD) (p q : ℕ) (hp : p < pd.k) (hq : q < pd.k) :
    ent (xint DEN pd) p q = ent pd.X0 p q * DEN + if p = q then deltaAt pd.Δ p * 2 ^ pd.s else 0 := by
  simp only [ent, xint]
  rw [xrowsF_getD DEN pd pd.k 0 pd.X0 p hp, xrowF_getD DEN _ _ pd.k 0 _ q hq, Nat.zero_add, Nat.zero_add, xdiag_eq]

theorem xint_spec {DEN : ℕ} (hD : 0 < DEN) (pd : BlockPD) (p q : Fin pd.k) :
    (ent (xint DEN pd) p q : ℝ) = ((2 ^ pd.s * DEN : ℕ) : ℝ) * pd.X DEN p q := by
  have e : ent (xint DEN pd) p q =
      ent pd.X0 p q * DEN + if (p : ℕ) = q then deltaAt pd.Δ p * 2 ^ pd.s else 0 :=
    ent_xint DEN pd p q p.isLt q.isLt
  rw [e]
  simp only [BlockPD.X, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply,
    smul_eq_mul, zpow_natCast]
  have hX0 : toMat pd.k pd.X0 p q = ent pd.X0 p q := rfl
  rw [hX0]
  have hDr : (DEN : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have h2 : (2 : ℝ) ^ pd.s ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases h : p = q
  · subst h
    simp only [if_true]
    push_cast
    field_simp
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h]
    push_cast
    field_simp
    ring

/-- A block part: the block's `ks`, `k`, `xint`, bases and tables. -/
def bpart (cuts : ℕ → CutData) (DEN : ℕ) (b : BCode) (pd : BlockPD) (fac : ℤ) (Pl Pr : List ℤ)
    (rhos : List (List (List (List ℤ)))) : PartData where
  ks := b.ks cuts
  k := pd.k
  X := xint DEN pd
  Bl := basisRows b Pl
  Br := basisRows b Pr
  fac := fac
  rhos := rhos
  w := 0
  bnd := 0
  folds := []
  Ks := []
  tree := []

/-- The block factor `S / (2^s · DEN)`. -/
def bfac (DEN S : ℕ) (pd : BlockPD) : ℤ := ((S / (2 ^ pd.s * DEN) : ℕ) : ℤ)

/-- A block's tagged parts, with `fac = S / (2^s · DEN)` (twice that for the `22` part of a coupled block). -/
def blockParts (cuts : ℕ → CutData) (DEN S : ℕ) (b : BCode) (pd : BlockPD) : List (Fam × PartData) :=
  match b.kind with
  | .word f _ => [(f, bpart cuts DEN b pd (bfac DEN S pd) b.Bp b.Bp (partRhos cuts b))]
  | .c3 =>
    [(.f31, bpart cuts DEN b pd (bfac DEN S pd) b.Bp b.Bp ((partRhos cuts b).map (rhoMap mT3_31))),
      (.f22, bpart cuts DEN b pd (2 * bfac DEN S pd) b.Bp b.Bvp ((partRhos cuts b).map (rhoMap mT3_22))),
      (.f13, bpart cuts DEN b pd (bfac DEN S pd) b.Bvp b.Bvp ((partRhos cuts b).map (rhoMap mT3_13)))]
  | .c23 =>
    [(.f31, bpart cuts DEN b pd (bfac DEN S pd) b.Bp b.Bp ((partRhos cuts b).map (rhoMap mT23_31))),
      (.f22, bpart cuts DEN b pd (2 * bfac DEN S pd) b.Bp b.Bvp ((partRhos cuts b).map (rhoMap mT23_22))),
      (.f13, bpart cuts DEN b pd (bfac DEN S pd) b.Bvp b.Bvp ((partRhos cuts b).map (rhoMap mT23_13)))]

theorem tval_eq (μ : Fam → Tup (Fin 3) → ℝ) (f : Fam) (P : PartData) :
    tval μ (f, P) = (P.fac : ℝ) * ∑ s, μ f s * (FTP P s : ℝ) := by
  rw [tval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast; ring

theorem bpart_fac (cuts : ℕ → CutData) (DEN : ℕ) (b : BCode) (pd : BlockPD) (fac : ℤ) (Pl Pr : List ℤ)
    (rhos : List (List (List (List ℤ)))) : (bpart cuts DEN b pd fac Pl Pr rhos).fac = fac := rfl

/-- `FTP` does not read `fac`. -/
theorem FTP_bpart (cuts : ℕ → CutData) (DEN : ℕ) (b : BCode) (pd : BlockPD) (fac : ℤ) (Pl Pr : List ℤ)
    (rhos : List (List (List (List ℤ)))) :
    FTP (bpart cuts DEN b pd fac Pl Pr rhos) = FTP (bpart cuts DEN b pd 0 Pl Pr rhos) := rfl

theorem sum_div' (g : Tup (Fin 3) → ℝ) (c : ℝ) : ∑ s, g s / c = (∑ s, g s) / c := (Finset.sum_div _ _ _).symm

/-- **One block.** `S ⟨X_b, L_b(μ)⟩` is the sum of its tagged parts' pairings. -/
theorem block_dec (cuts : ℕ → CutData) {DEN : ℕ} (hD : 0 < DEN) (S : ℕ) (b : BCode) (pd : BlockPD)
    (hpd : pdChk DEN pd = true) (hS : S % (2 ^ pd.s * DEN) = 0) (μ : Fam → Tup (Fin 3) → ℝ) :
    (S : ℝ) * ∑ i, ∑ i', pd.X DEN i i' * (b.toSpec cuts pd.k).L μ i i' =
      ((blockParts cuts DEN S b pd).map (tval μ)).sum := by
  have hc : ((2 ^ pd.s * DEN : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.pow_pos (by norm_num)) hD).ne'
  have hX := xint_spec hD pd
  have hsym : (pd.X DEN)ᵀ = pd.X DEN := by
    have h := (BlockPD.X_posDef hpd).1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hS1 : (S : ℝ) = (bfac DEN S pd : ℝ) * ((2 ^ pd.s * DEN : ℕ) : ℝ) := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hS)
    rw [bfac]
    exact_mod_cast this.symm
  cases hk : b.kind with
  | word f T =>
    rw [pair_word cuts b pd.k (pd.X DEN) (xint DEN pd) _ hc hX hk (bpart cuts DEN b pd 0 b.Bp b.Bp _)
      rfl rfl rfl rfl rfl rfl μ]
    simp only [blockParts, hk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval_eq,
      bpart_fac, partRhos]
    rw [FTP_bpart _ _ _ _ (bfac DEN S pd), sum_div', hS1]
    field_simp
  | c3 =>
    rw [pair_c3 cuts b pd.k (pd.X DEN) (xint DEN pd) _ hc hX hk hsym
      (bpart cuts DEN b pd 0 b.Bp b.Bp _) (bpart cuts DEN b pd 0 b.Bp b.Bvp _)
      (bpart cuts DEN b pd 0 b.Bvp b.Bvp _) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ μ]
    simp only [blockParts, hk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval_eq,
      bpart_fac, partRhos]
    rw [FTP_bpart _ _ _ _ (bfac DEN S pd), FTP_bpart _ _ _ _ (2 * bfac DEN S pd), FTP_bpart _ _ _ _ (bfac DEN S pd),
      sum_div', sum_div', sum_div', hS1]
    push_cast
    field_simp
    ring
  | c23 =>
    rw [pair_c23 cuts b pd.k (pd.X DEN) (xint DEN pd) _ hc hX hk hsym
      (bpart cuts DEN b pd 0 b.Bp b.Bp _) (bpart cuts DEN b pd 0 b.Bp b.Bvp _)
      (bpart cuts DEN b pd 0 b.Bvp b.Bvp _) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ μ]
    simp only [blockParts, hk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval_eq,
      bpart_fac, partRhos]
    rw [FTP_bpart _ _ _ _ (bfac DEN S pd), FTP_bpart _ _ _ _ (2 * bfac DEN S pd), FTP_bpart _ _ _ _ (bfac DEN S pd),
      sum_div', sum_div', sum_div', hS1]
    push_cast
    field_simp
    ring

end LayerDT0

#print axioms LayerDT0.regroup
#print axioms LayerDT0.block_dec
