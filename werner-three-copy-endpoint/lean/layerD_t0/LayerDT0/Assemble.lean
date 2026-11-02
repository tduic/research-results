import LayerDT0.Sites
import LayerDT0.Rows
import LayerDT0.PD

/-!
# Layer D (t = 0): assembling the certificate into `endpoint_of_t0_cert`

* `CutData`: one cut `T` with its table and its site and qubit modules; `CutData.Good` is
  obligations 2–4 for all of them (`IsCut`, `TabAt` for `d ≥ 4`, `SiteCert`, `QubitAt`).
* `BCode`: one block of `blocks.jsonl` — its spec (kind and cut), its module indices `rs`, `rq`
  and its basis `B` (and `Bv` for coupled blocks) as packed rows in the verifier's Kronecker order
  `((a₀ k₁ + a₁) k₂ + a₂) k_q + c`.
* `BCode.toSpec`: the `BlockSpec (Fin 3)`; `BCode.valid`: it is `Valid` when its cut data is good,
  its kind's cut is the cut's `T` and the module indices are in range.
* `endpoint_of_data`: `endpoint_of_t0_cert` for lists of codes, multipliers (`BlockPD`), row codes
  and `λ`, with every hypothesis except the identity `hid` discharged by Boolean checks.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint LayerDProto

/-- A qubit module: `k_q`, `J` (16 rows) and `Fq` (24 matrices). -/
structure QubData where
  k : ℕ
  J : List (List ℤ)
  F : List (List (List ℤ))

instance : Inhabited QubData := ⟨⟨0, [], []⟩⟩

instance : Inhabited SiteData := ⟨⟨0, [], [], [], [], 0, [], 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

structure CutData where
  T : Finset (Fin 4)
  tab : P4 → P4 → P4 × ℕ
  sites : List SiteData
  qubs : List QubData

def CutData.Good (c : CutData) : Prop :=
  IsCut c.T ∧ (∀ d, 4 ≤ d → TabAt c.T d c.tab) ∧
    (∀ s ∈ c.sites, SiteCert c.tab (NP s.k s.N)) ∧ (∀ q ∈ c.qubs, QubitAt c.T (qF q.k q.F) (qJ q.k q.J))

/-- One block of the certificate (everything but the multiplier). -/
structure BCode where
  kind : BKind
  cut : ℕ
  rs : List ℕ
  rq : ℕ
  bb : ℕ
  ncol : ℕ
  Bp : List ℤ
  Bvp : List ℤ

instance : Inhabited BCode := ⟨⟨.c3, 0, [], 0, 1, 0, [], []⟩⟩

section Spec
variable (cuts : ℕ → CutData)

def BCode.cd (b : BCode) : CutData := cuts b.cut
def BCode.site (b : BCode) (i : Fin 3) : SiteData := (b.cd cuts).sites.getD (b.rs.getD i 0) default
def BCode.qub (b : BCode) : QubData := (b.cd cuts).qubs.getD b.rq default

/-- The verifier's flat module index of `((aᵢ)ᵢ, c)`. -/
def flatIdx (k : Fin 3 → ℕ) (kq : ℕ) (a : Fin 3 → ℕ) (c : ℕ) : ℕ :=
  ((a 0 * k 1 + a 1) * k 2 + a 2) * kq + c

/-- The basis as a real matrix on the module index. -/
noncomputable def basisMat (k : Fin 3 → ℕ) (kq bb ncol : ℕ) (P : List ℤ) (n : ℕ) :
    Matrix (((i : Fin 3) → Fin (k i)) × Fin kq) (Fin n) ℝ :=
  Matrix.of fun x col => (g2 (P.map (unpk bb ncol)) (flatIdx k kq (fun i => x.1 i) x.2) col : ℝ)

/-- **The block specification** of a code, with `n` columns. -/
noncomputable def BCode.toSpec (b : BCode) (n : ℕ) : BlockSpec (Fin 3) where
  kind := b.kind
  tab := (b.cd cuts).tab
  k := fun i => (b.site cuts i).k
  N := fun i => NP _ (b.site cuts i).N
  kq := (b.qub cuts).k
  Fq := qF _ (b.qub cuts).F
  J := qJ _ (b.qub cuts).J
  n := n
  B := basisMat (fun i => (b.site cuts i).k) (b.qub cuts).k b.bb b.ncol b.Bp n
  Bv := basisMat (fun i => (b.site cuts i).k) (b.qub cuts).k b.bb b.ncol b.Bvp n

/-- The Boolean side conditions of a code (given the cut table `T`). -/
def BCode.ok (T : ℕ → Finset (Fin 4)) (ns nq : ℕ → ℕ) (b : BCode) : Bool :=
  decide (b.kind.cut = T b.cut) && b.rs.length == 3 && b.rs.all (· < ns b.cut) && decide (b.rq < nq b.cut)

theorem BCode.valid {b : BCode} (hcd : (b.cd cuts).Good) (hcut : b.kind.cut = (b.cd cuts).T)
    (hrs : ∀ i : Fin 3, b.rs.getD i 0 < (b.cd cuts).sites.length) (hrq : b.rq < (b.cd cuts).qubs.length)
    (n : ℕ) : (b.toSpec cuts n).Valid := by
  obtain ⟨hT, htab, hs, hq⟩ := hcd
  refine ⟨?_, ?_, fun i => ?_, ?_⟩
  · show IsCut b.kind.cut; rw [hcut]; exact hT
  · intro d hd; show TabAt b.kind.cut d _; rw [hcut]; exact htab d hd
  · exact hs _ (by rw [BCode.site, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hrs i), Option.getD_some]; exact List.getElem_mem _)
  · show QubitAt b.kind.cut _ _; rw [hcut]
    exact hq _ (by rw [BCode.qub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrq, Option.getD_some]; exact List.getElem_mem _)

theorem BCode.valid_of_ok {T : ℕ → Finset (Fin 4)} {ns nq : ℕ → ℕ}
    (hT : ∀ c, (cuts c).T = T c) (hns : ∀ c, (cuts c).sites.length = ns c)
    (hnq : ∀ c, (cuts c).qubs.length = nq c) {b : BCode} (hcd : (b.cd cuts).Good)
    (h : b.ok T ns nq = true) (n : ℕ) : (b.toSpec cuts n).Valid := by
  simp only [BCode.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hcut, hlen⟩, hrs⟩, hrq⟩ := h
  refine BCode.valid cuts hcd (by rw [BCode.cd, hT]; exact hcut) (fun i => ?_) (by rw [BCode.cd, hnq]; exact hrq) n
  rw [BCode.cd, hns]
  exact hrs _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt), Option.getD_some]; exact List.getElem_mem _)

end Spec

theorem all_getD {α : Type*} [Inhabited α] {f : α → Bool} {l : List α} (h : l.all f = true) {j : ℕ}
    (hj : j < l.length) : f (l.getD j default) = true := by
  rw [List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact h _ (List.getElem_mem hj)

/-! ### The whole certificate -/

/-- The multiplier `λ_r = num / den`. -/
noncomputable def lamOf (num : List ℤ) (den : ℕ) (r : ℕ) : ℝ := (num.getD r 0 : ℝ) / den

/-- Trace rows carry a nonnegative multiplier (`(F)` of the verifier). -/
def lamOK (codes : List RowCode) (num : List ℤ) (n : ℕ) : Bool :=
  (List.range n).all fun r => match rowAt codes r with
    | .trace => decide (0 ≤ num.getD r 0)
    | _ => true

theorem hval_of_lamOK {codes : List RowCode} {num : List ℤ} {den n : ℕ} (h : lamOK codes num n = true) :
    0 ≤ ∑ r : Fin n, lamOf num den r * (rowAt codes r).val := by
  refine Finset.sum_nonneg fun r _ => ?_
  have hr := all_range h r.isLt
  cases hc : rowAt codes r with
  | trace =>
    rw [hc] at hr
    simp only [decide_eq_true_eq] at hr
    simp only [RowCode.val, lamOf]
    have : (0 : ℝ) ≤ (num.getD r 0 : ℝ) := by exact_mod_cast hr
    positivity
  | contrast => simp [RowCode.val]
  | r3122 => simp [RowCode.val]
  | r2213 => simp [RowCode.val]

/-- **The `t = 0` endpoint from explicit data, up to the identity.** Every hypothesis of
`endpoint_of_t0_cert` other than `hid` is discharged: block validity from the cut data and the
codes' checks, `X_b ≻ 0` from `pdChk`, the rows from `RowCode.ok`, `∑ λ v ≥ 0` from `lamOK`. -/
theorem endpoint_of_data (cuts : ℕ → CutData) (T : ℕ → Finset (Fin 4)) (ns nq : ℕ → ℕ)
    (hT : ∀ c, (cuts c).T = T c) (hns : ∀ c, (cuts c).sites.length = ns c)
    (hnq : ∀ c, (cuts c).qubs.length = nq c)
    (hcuts : ∀ c, (cuts c).Good) (nb : ℕ) (bcs : List BCode)
    (hbc : ∀ j < nb, (bcs.getD j default).ok T ns nq = true)
    (DEN : ℕ) (pds : List BlockPD) (hpd : pds.all (pdChk DEN) = true) (hlen : nb ≤ pds.length)
    (nr : ℕ) (codes : List RowCode) (hcodes : codes.all RowCode.ok = true)
    (num : List ℤ) (den : ℕ) (hlam : lamOK codes num nr = true)
    (hid : ∀ μ : Fam → Tup (Fin 3) → ℝ, OrbInv (Fin 3) μ →
      mObj 2 μ = ∑ j : Fin nb, ∑ i, ∑ i', (pds.getD j default).X DEN i i' *
          ((bcs.getD j default).toSpec cuts (pds.getD j default).k).L μ i i' +
        ∑ r : Fin nr, lamOf num den r * mRowVal 2 (rowAt codes r).row μ)
    (e : ℕ) (C : Matrix (Fin 3 → Fin e) (Fin 3 → Fin e) ℂ) (hC : C.rank ≤ 2) : 0 ≤ qfun C :=
  endpoint_of_t0_cert (β := Fin nb) (fun j => (bcs.getD j default).toSpec cuts (pds.getD j default).k)
    (fun j => BCode.valid_of_ok cuts hT hns hnq (hcuts _) (hbc j j.isLt) _)
    (fun j => (pds.getD j default).X DEN)
    (fun j => (BlockPD.X_posDef (pdChk_getD hpd (lt_of_lt_of_le j.isLt hlen))).posSemidef)
    (γ := Fin nr) (fun r => (rowAt codes r).row) (fun r => lamOf num den r) (fun r => (rowAt codes r).val)
    (fun r => (rowAt codes r).valid (rowAt_ok hcodes r)) (hval_of_lamOK hlam) hid e C hC

end LayerDT0

#print axioms LayerDT0.endpoint_of_data
