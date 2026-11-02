import LayerDProto.R2RecompKernel

/-!
# Layer D (t = 0): `ycoreOK` row slice by row slice (core Lean)

For the largest coupled parts one `ycoreOK` declaration needs more than 3 GB in the kernel (block 917, `k = 62`,
192 rows: 3.6 GB). `yRows k w X B_l B_r` is `B_l.map (fun row => dot row Z)`, so its rows can be compared in
slices of `B_l`'s rows, one declaration (and module) each:

* `yframeOK`: every conjunct of `ycoreOK` except the comparison of the packed rows;
* `ySl … lo n`: the packed rows `lo … lo+n−1` (`yRows` of `(B_l.drop lo).take n`);
* **`ycoreOK_of_slices`**: `yframeOK` and equal slices at `lo = 0, n, 2n, …` covering `B_l` give `ycoreOK`.
-/

namespace LayerDT0

open LayerDProto

/-- `ycoreOK` without the comparison of the packed rows. -/
def yframeOK (w : Nat) (P P' : PartData) : Bool :=
  P.ks == P'.ks && P.fac == P'.fac && P.rhos == P'.rhos &&
  (P'.Bl.length == P.Bl.length && P'.Br.length == P.Br.length && decide (0 < w) &&
  isRect P.k P.k P.X && P.Bl.all (·.length == P.k) && P.Br.all (·.length == P.k) &&
  isRect P'.k P'.k P'.X && P'.Bl.all (·.length == P'.k) && P'.Br.all (·.length == P'.k) &&
  decide (4 * (rowSumMax P.Bl * entMax P.X * rowSumMax P.Br) < 2 ^ w) &&
  decide (4 * (rowSumMax P'.Bl * entMax P'.X * rowSumMax P'.Br) < 2 ^ w))

/-- The packed rows `lo … lo+n−1` of `B_l X B_rᵀ`. -/
def ySl (w : Nat) (P : PartData) (lo n : Nat) : List Int := yRows P.k w P.X ((P.Bl.drop lo).take n) P.Br

theorem ySl_eq (w : Nat) (P : PartData) (lo n : Nat) :
    ySl w P lo n = ((yRows P.k w P.X P.Bl P.Br).drop lo).take n := by
  simp only [ySl, yRows, List.map_drop, List.map_take]

theorem yRows_length (k w : Nat) (X Bl Br : List (List Int)) : (yRows k w X Bl Br).length = Bl.length := by
  simp [yRows]

theorem eq_of_slices {L L' : List Int} (n c : Nat) (hn : 0 < n) (hl : L.length = L'.length)
    (hc : L.length ≤ c * n)
    (h : ∀ g, g < c → (L.drop (g * n)).take n = (L'.drop (g * n)).take n) : L = L' := by
  apply List.ext_getElem hl
  intro i h1 h2
  have hg : i / n < c := by
    rcases Nat.lt_or_ge (i / n) c with h' | h'
    · exact h'
    · exfalso
      have := Nat.mul_le_mul_right n h'
      have := Nat.div_mul_le_self i n
      have := Nat.lt_div_mul_add (a := i) hn
      omega
  have e := congrArg (fun l => l[i - i / n * n]?) (h (i / n) hg)
  simp only at e
  have hlt : i - i / n * n < n := by
    have := Nat.lt_div_mul_add (a := i) hn
    have := Nat.div_mul_le_self i n
    omega
  have hle : i / n * n ≤ i := Nat.div_mul_le_self i n
  rw [List.getElem?_take_of_lt hlt, List.getElem?_take_of_lt hlt, List.getElem?_drop, List.getElem?_drop,
    Nat.add_sub_cancel' hle, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at e
  exact Option.some.inj e

/-- **`ycoreOK` from its frame and row slices.** -/
theorem ycoreOK_of_slices (w : Nat) (P P' : PartData) (n c : Nat) (hn : 0 < n) (hf : yframeOK w P P' = true)
    (hc : P.Bl.length ≤ c * n)
    (hs : ∀ g, g < c → (ySl w P (g * n) n == ySl w P' (g * n) n) = true) : ycoreOK w P P' = true := by
  simp only [yframeOK, Bool.and_eq_true] at hf
  have hy : yRows P.k w P.X P.Bl P.Br = yRows P'.k w P'.X P'.Bl P'.Br := by
    have hlen : P'.Bl.length = P.Bl.length := by
      have := hf.2.1.1.1.1.1.1.1.1.1.1
      simpa using this
    refine eq_of_slices n c hn (by rw [yRows_length, yRows_length, hlen]) (by rw [yRows_length]; exact hc)
      fun g hg => ?_
    have := hs g hg
    rw [ySl_eq, ySl_eq] at this
    simpa using this
  simp only [ycoreOK, yEqOK, Bool.and_eq_true, beq_iff_eq]
  simp only [beq_iff_eq] at hf
  exact ⟨hf.1, ⟨hf.2, hy⟩⟩

end LayerDT0

#print axioms LayerDT0.ycoreOK_of_slices
