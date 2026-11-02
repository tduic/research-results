import LayerDT0.Basic

/-!
# Layer D (t = 0): the equality rows (`RowValid`)

`verify_t0.py`'s `ROWDEF` has four kinds of rows, each twice a trace functional:

* the trace row `2 Tr Ŷ31` (value `2`);
* contrast rows `2 Tr[P_(w,wq) Ŷ_f] − c Tr[P_(w, removeSlot wq r) Ŷ_f]` for `(f, r) = (31, 0), (22, 0), (13, 3)`;
* 31–22 rows `2 Tr[P_w Ŷ31] − 2 Tr[P_w Ŷ22]` (every component fixes slot 2);
* 22–13 rows `2 Tr[P_w Ŷ22] − 2 Tr[P_{π w π⁻¹} Ŷ13]` (every component fixes slot 1, `π = PI_ABB`).

A row is encoded by its kind and the verifier's `PERMS` indices (`RowCode`); `RowCode.row` is the
`Row (Fin 3)` and `RowCode.ok` the side conditions, checked by the kernel. `RowCode.valid`: an
`ok` code is physically valid (`RowValid`), by layer AllD's `rowValid_*` lemmas.
-/

namespace LayerDT0

open WernerEndpoint

inductive RowCode
  | trace
  | contrast (f : Fam) (r : Fin 4) (w0 w1 w2 wq : Fin 24)
  | r3122 (w0 w1 w2 wq : Fin 24)
  | r2213 (w0 w1 w2 wq : Fin 24)

/-- The three site words. -/
def wOf (w0 w1 w2 : Fin 24) : Fin 3 → P4 := ![permTab w0, permTab w1, permTab w2]

noncomputable def RowCode.row : RowCode → Row (Fin 3)
  | .trace => [(2, .f31, ((fun _ => (1 : P4)), (1 : P4)))]
  | .contrast f r w0 w1 w2 wq =>
      [(2, f, (wOf w0 w1 w2, permTab wq)),
        (-(if permTab wq r = r then 2 else 1), f, (wOf w0 w1 w2, removeSlot (permTab wq) r))]
  | .r3122 w0 w1 w2 wq => [(2, .f31, (wOf w0 w1 w2, permTab wq)), (-2, .f22, (wOf w0 w1 w2, permTab wq))]
  | .r2213 w0 w1 w2 wq =>
      [(2, .f22, (wOf w0 w1 w2, permTab wq)),
        (-2, .f13, (fun i => piABB * wOf w0 w1 w2 i * piABB⁻¹, piABB * permTab wq * piABB⁻¹))]

noncomputable def RowCode.val : RowCode → ℝ
  | .trace => 2
  | _ => 0

/-- Slot `r` is fixed by the three site words. -/
def fixes3 (w0 w1 w2 : Fin 24) (r : Fin 4) : Bool :=
  permFun w0 r == r && permFun w1 r == r && permFun w2 r == r

def RowCode.ok : RowCode → Bool
  | .trace => true
  | .contrast f r w0 w1 w2 _ => !famPat f r && fixes3 w0 w1 w2 r
  | .r3122 w0 w1 w2 wq => fixes3 w0 w1 w2 2 && permFun wq 2 == 2
  | .r2213 w0 w1 w2 wq => fixes3 w0 w1 w2 1 && permFun wq 1 == 1

theorem fixes3_spec {w0 w1 w2 : Fin 24} {r : Fin 4} (h : fixes3 w0 w1 w2 r = true) :
    ∀ i, wOf w0 w1 w2 i r = r := by
  simp only [fixes3, Bool.and_eq_true, beq_iff_eq] at h
  intro i
  fin_cases i
  exacts [h.1.1, h.1.2, h.2]

theorem RowCode.valid (c : RowCode) (h : c.ok = true) : RowValid (Fin 3) c.row c.val := by
  cases c with
  | trace => exact rowValid_trace 2
  | contrast f r w0 w1 w2 wq =>
    simp only [RowCode.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact rowValid_contrast f r h.1 _ _ (fixes3_spec h.2)
  | r3122 w0 w1 w2 wq =>
    simp only [RowCode.ok, Bool.and_eq_true, beq_iff_eq] at h
    exact rowValid_31_22 _ _ (fixes3_spec h.1) h.2
  | r2213 w0 w1 w2 wq =>
    simp only [RowCode.ok, Bool.and_eq_true, beq_iff_eq] at h
    exact rowValid_22_13 _ _ (fixes3_spec h.1) h.2

/-- Row codes from a list (default: the trace row, which is `ok`). -/
def rowAt (l : List RowCode) (r : ℕ) : RowCode := l.getD r .trace

theorem rowAt_ok {l : List RowCode} (h : l.all RowCode.ok = true) (r : ℕ) : (rowAt l r).ok = true := by
  unfold rowAt
  rw [List.getD_eq_getElem?_getD]
  cases hr : l[r]? with
  | none => rfl
  | some c =>
    rw [List.all_eq_true] at h
    exact h c (List.mem_of_getElem? hr)

end LayerDT0

#print axioms LayerDT0.RowCode.valid
#print axioms LayerDT0.rowAt_ok
