import WernerEndpoint.LayerC_BrauerCore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Layer C: kernel-checkable component certificates for four replicas

* `permTab : Fin 24 → Perm (Fin 4)` is `PERMS` of `verify_d5.py` (lexicographic order);
  `permTab_surj`: every permutation of `Fin 4` is listed.
* `muT T i` is the slot map of `Γ_T(P_{permTab i})`; `muC row` reads the same map from a packed
  table (faster for the kernel), and the generated files prove `muC row = muT T` by `decide`.
* `PairCert.ofNat` decodes one packed certificate (152 bits: `u`, `c`, and 12 × (root, rank,
  parent edge)); `BrCertB` is a Boolean form of `BrCert` for `R = Fin 4` over explicit lists,
  and `brCertB_sound` proves `BrCertB … = true → BrCert …`.
* `chkB rows muRow i j` checks the certificate of the product `Γ_T(P_i) Γ_T(P_j)`;
  `chkB_sound` turns a successful check into `BrCert`, hence (by `br_mul_br`) into
  `br (muT T i) * br (muT T j) = |α|^c • br (muT T u)` for every local dimension.
-/

set_option linter.unusedSectionVars false

namespace WernerEndpoint

/-- `PERMS` of `verify_d5.py`, `permFun i k = PERMS[i][k]`. -/
def permFun : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0],
    ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

/-- The inverse permutations. -/
def permInv : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1],
    ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2], ![2, 3, 0, 1], ![3, 2, 0, 1],
    ![1, 2, 3, 0], ![1, 3, 2, 0], ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]]

theorem permInv_permFun : ∀ i x, permInv i (permFun i x) = x := by decide
theorem permFun_permInv : ∀ i x, permFun i (permInv i x) = x := by decide

/-- The 24 permutations of `Fin 4`, in `verify_d5.py`'s order. -/
def permTab (i : Fin 24) : Equiv.Perm (Fin 4) :=
  ⟨permFun i, permInv i, permInv_permFun i, permFun_permInv i⟩

theorem permTab_apply (i : Fin 24) (k : Fin 4) : permTab i k = permFun i k := rfl

theorem permTab_surj : ∀ p : Equiv.Perm (Fin 4), ∃ i, permTab i = p := by decide

/-- The slot map of `Γ_T(P_{permTab i})`. -/
def muT (T : Finset (Fin 4)) (i : Fin 24) : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 :=
  fun q => tauT T (permMatch (permTab i) (tauT T q))

/-- Bits `off … off + w - 1` of `n`. -/
def bitsAt (n off w : ℕ) : ℕ := Nat.mod (Nat.shiftRight n off) (Nat.pow 2 w)

def fin4 (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

def fin24 (n : ℕ) : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by decide)⟩

/-- Slot codes: row digit `k`, column digit `4 + k`. -/
def encS : Fin 4 ⊕ Fin 4 → ℕ
  | .inl k => k.val
  | .inr k => k.val + 4

def decS (n : ℕ) : Fin 4 ⊕ Fin 4 := if n % 8 < 4 then .inl (fin4 n) else .inr (fin4 n)

/-- Vertex codes: top `k`, bottom `4 + k`, middle `8 + k`. -/
def encV : Vtx (Fin 4) → ℕ
  | .inl k => k.val
  | .inr (.inr k) => k.val + 4
  | .inr (.inl k) => k.val + 8

def decV (n : ℕ) : Vtx (Fin 4) :=
  if n < 4 then .inl (fin4 n) else if n < 8 then .inr (.inr (fin4 n)) else .inr (.inl (fin4 n))

/-- Edge codes: first factor `encS q`, second factor `8 + encS q`. -/
def decE (n : ℕ) : (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4) :=
  if n < 8 then .inl (decS n) else .inr (decS n)

/-- A slot map read from a packed table (4 bits per slot). -/
def muC (row : Fin 24 → ℕ) (i : Fin 24) (q : Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 :=
  decS (bitsAt (row i) (4 * encS q) 4)

/-- A decoded component certificate. -/
structure PairCert where
  u : Fin 24
  c : ℕ
  root : Vtx (Fin 4) → Vtx (Fin 4)
  rank : Vtx (Fin 4) → ℕ
  pe : Vtx (Fin 4) → (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)

/-- Decode one packed certificate. -/
def PairCert.ofNat (e : ℕ) : PairCert :=
  ⟨fin24 (bitsAt e 0 5), bitsAt e 5 3, fun v => decV (bitsAt e (8 + 4 * encV v) 4),
    fun v => bitsAt e (56 + 4 * encV v) 4, fun v => decE (bitsAt e (104 + 4 * encV v) 4)⟩

/-- The certificate of the pair `(i, j)` in a packed table (row `i`, bits `152 j …`). -/
def certOf (rows : Fin 24 → ℕ) (i j : Fin 24) : PairCert :=
  PairCert.ofNat (bitsAt (rows i) (152 * j.val) 152)

def allS : List (Fin 4 ⊕ Fin 4) := [.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

def allV : List (Vtx (Fin 4)) :=
  [.inl 0, .inl 1, .inl 2, .inl 3, .inr (.inl 0), .inr (.inl 1), .inr (.inl 2), .inr (.inl 3),
    .inr (.inr 0), .inr (.inr 1), .inr (.inr 2), .inr (.inr 3)]

def allE : List ((Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) := allS.map .inl ++ allS.map .inr

theorem mem_allS : ∀ q, q ∈ allS := by
  rintro (k | k) <;> fin_cases k <;> simp [allS]
theorem mem_allV : ∀ v, v ∈ allV := by
  rintro (k | k | k) <;> fin_cases k <;> simp [allV]
theorem mem_allE : ∀ e, e ∈ allE := by
  rintro (q | q) <;> simp [allE, mem_allS]

/-- `BrCert` as a Boolean computation over explicit lists (`R = Fin 4`). -/
def BrCertB (μ ν lam : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4) (root : Vtx (Fin 4) → Vtx (Fin 4))
    (rank : Vtx (Fin 4) → ℕ) (pe : Vtx (Fin 4) → (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) (c : ℕ) :
    Bool :=
  allE.all (fun e => decide (root (edge μ ν e).1 = root (edge μ ν e).2)) &&
  allV.all (fun v => decide (root (root v) = root v)) &&
  allV.all (fun v => decide (root v ≠ v →
    ((edge μ ν (pe v)).1 = v ∧ rank (edge μ ν (pe v)).2 < rank v ∧
        root (edge μ ν (pe v)).2 = root v) ∨
      ((edge μ ν (pe v)).2 = v ∧ rank (edge μ ν (pe v)).1 < rank v ∧
        root (edge μ ν (pe v)).1 = root v))) &&
  allS.all (fun q => decide (root (eo q) = root (eo (lam q)))) &&
  allS.all (fun q => decide (root (eo q) = eo q ∨ root (eo q) = eo (lam q))) &&
  decide (c = (if root (.inr (.inl 0)) = .inr (.inl 0) then 1 else 0) +
    (if root (.inr (.inl 1)) = .inr (.inl 1) then 1 else 0) +
    (if root (.inr (.inl 2)) = .inr (.inl 2) then 1 else 0) +
    (if root (.inr (.inl 3)) = .inr (.inl 3) then 1 else 0))

theorem brCertB_sound {μ ν lam : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4} {root : Vtx (Fin 4) → Vtx (Fin 4)}
    {rank : Vtx (Fin 4) → ℕ} {pe : Vtx (Fin 4) → (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)} {c : ℕ}
    (h : BrCertB μ ν lam root rank pe c = true) : BrCert μ ν lam root rank pe c := by
  simp only [BrCertB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun e => h1 e (mem_allE e), fun v => h2 v (mem_allV v), fun v => h3 v (mem_allV v),
    fun q => h4 q (mem_allS q), fun q => h5 q (mem_allS q), ?_⟩
  rw [h6, Finset.card_filter, Fin.sum_univ_four]

/-- The check of the pair `(i, j)` of a packed certificate table, slot maps from `muRow`. -/
def chkB (rows muRow : Fin 24 → ℕ) (i j : Fin 24) : Bool :=
  let d := certOf rows i j
  BrCertB (muC muRow i) (muC muRow j) (muC muRow d.u) d.root d.rank d.pe d.c

theorem chkB_sound {rows muRow : Fin 24 → ℕ} {T : Finset (Fin 4)}
    (hmu : ∀ i q, muC muRow i q = muT T i q) {i j : Fin 24} (h : chkB rows muRow i j = true) :
    BrCert (muT T i) (muT T j) (muT T (certOf rows i j).u) (certOf rows i j).root
      (certOf rows i j).rank (certOf rows i j).pe (certOf rows i j).c := by
  have e : ∀ k, muC muRow k = muT T k := fun k => funext (hmu k)
  have h' := brCertB_sound h
  rw [e, e, e] at h'
  exact h'

end WernerEndpoint

#print axioms WernerEndpoint.permTab_surj
#print axioms WernerEndpoint.brCertB_sound
#print axioms WernerEndpoint.chkB_sound
