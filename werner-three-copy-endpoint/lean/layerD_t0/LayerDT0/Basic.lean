import WernerEndpoint.AllD_Cert

/-!
# Layer D (t = 0): shared helpers and the qubit modules (`QubitAt`)

* `permIdx`: the `verify_t0.py` index of a permutation (`permIdx (permTab i) = i`).
* `g1`, `g2`, `g3`: total list lookups (default `0`) for generated integer data.
* `sum_Osite`: a sum against `Γ_T(P_p)` collapses to one sum over the column index:
  `∑_{x,y} f x y Γ_T(P_p)_{xy} = ∑_u f (mix u (u∘p)) (mix (u∘p) u)`.
* `qubitAt_of_chk`: a Boolean check on integer data (`qubChk`) gives `QubitAt`.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace LayerDT0

open WernerEndpoint

/-! ### Indices and lookups -/

/-- The index of a permutation in the verifier's `PERMS` order (`0` if not found, never). -/
def permIdx (p : P4) : ℕ :=
  (List.range 24).findIdx fun i =>
    permFun (fin24 i) 0 == p 0 && permFun (fin24 i) 1 == p 1 && permFun (fin24 i) 2 == p 2

theorem permIdx_permTab : ∀ i : Fin 24, permIdx (permTab i) = i.val := by decide

theorem fin24_val (i : Fin 24) : fin24 i.val = i := by
  ext; simp [fin24, Nat.mod_eq_of_lt i.isLt]

def g1 (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0
def g2 (l : List (List ℤ)) (i j : ℕ) : ℤ := (l.getD i []).getD j 0
def g3 (l : List (List (List ℤ))) (i j k : ℕ) : ℤ := ((l.getD i []).getD j []).getD k 0

theorem all_range {n : ℕ} {f : ℕ → Bool} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) :
    f i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

/-! ### Sums against `Γ_T(P_p)` -/

/-- Exchange of the factors in `T` between two index tuples. -/
def mixV {α : Type*} (T : Finset (Fin 4)) (x y : Fin 4 → α) : Fin 4 → α :=
  fun r => if r ∈ T then y r else x r

theorem mixV_mixV {α : Type*} (T : Finset (Fin 4)) (x y : Fin 4 → α) :
    mixV T (mixV T x y) (mixV T y x) = x := by
  funext r; by_cases h : r ∈ T <;> simp [mixV, h]

theorem Osite_apply (T : Finset (Fin 4)) (α : Type*) [Fintype α] [DecidableEq α] (p : P4)
    (x y : Fin 4 → α) :
    Osite T α p x y = if mixV T y x = mixV T x y ∘ p then 1 else 0 := rfl

/-- The pair involution `(x, y) ↦ (mix x y, mix y x)`. -/
def mixE {α : Type*} (T : Finset (Fin 4)) : (Fin 4 → α) × (Fin 4 → α) ≃ (Fin 4 → α) × (Fin 4 → α) where
  toFun z := (mixV T z.1 z.2, mixV T z.2 z.1)
  invFun z := (mixV T z.1 z.2, mixV T z.2 z.1)
  left_inv z := by simp [mixV_mixV]
  right_inv z := by simp [mixV_mixV]

theorem sum_Osite (T : Finset (Fin 4)) {α : Type*} [Fintype α] [DecidableEq α] (p : P4)
    (f : (Fin 4 → α) → (Fin 4 → α) → ℂ) :
    ∑ x, ∑ y, f x y * Osite T α p x y = ∑ u, f (mixV T u (u ∘ p)) (mixV T (u ∘ p) u) := by
  rw [← Fintype.sum_prod_type' (fun x y => f x y * Osite T α p x y)]
  rw [← (mixE (α := α) T).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [mixE, Equiv.coe_fn_mk, Osite_apply, mixV_mixV, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (u ∘ p)]
  simp

/-! ### The qubit index `Fin 4 → Fin 2` as `0 … 15` (verifier order: slot 0 most significant) -/

def dec2 (n : ℕ) : Fin 4 → Fin 2 := fun r => ⟨(n / 2 ^ (3 - r.val)) % 2, Nat.mod_lt _ (by decide)⟩

def enc2 (x : Fin 4 → Fin 2) : ℕ := ((x 0 * 2 + x 1) * 2 + x 2) * 2 + x 3

theorem enc2_lt : ∀ x : Fin 4 → Fin 2, enc2 x < 16 := by decide
theorem dec2_enc2 : ∀ x : Fin 4 → Fin 2, dec2 (enc2 x) = x := by decide
theorem enc2_dec2 : ∀ n < 16, enc2 (dec2 n) = n := by decide

theorem sum_fin42 {M : Type*} [AddCommMonoid M] (g : (Fin 4 → Fin 2) → M) :
    ∑ u, g u = ((List.range 16).map fun n => g (dec2 n)).sum := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_nbij' enc2 dec2 (fun x _ => by simpa using enc2_lt x)
    (fun _ _ => Finset.mem_univ _) (fun x _ => dec2_enc2 x)
    (fun n hn => enc2_dec2 n (by simpa using hn)) (fun x _ => by rw [dec2_enc2])

/-! ### Qubit modules -/

/-- `J` from a 16-row integer table (row `enc2 x`). -/
def qJ (kq : ℕ) (Jl : List (List ℤ)) : Matrix (Fin 4 → Fin 2) (Fin kq) ℝ :=
  Matrix.of fun x a => (g2 Jl (enc2 x) a : ℝ)

/-- `Fq(p)` from 24 integer `kq × kq` tables (index `permIdx p`). -/
def qF (kq : ℕ) (Fl : List (List (List ℤ))) : P4 → Matrix (Fin kq) (Fin kq) ℝ :=
  fun p => Matrix.of fun a b => (g3 Fl (permIdx p) a b : ℝ)

/-- The kernel check `Fq(p) = Jᵀ Γ_T(P_p) J` at `d = 2` (via `sum_Osite`). -/
def qubChk (T : Finset (Fin 4)) (kq : ℕ) (Jl : List (List ℤ)) (Fl : List (List (List ℤ))) : Bool :=
  (List.range 24).all fun i => (List.range kq).all fun a => (List.range kq).all fun b =>
    g3 Fl i a b == ((List.range 16).map fun n =>
      g2 Jl (enc2 (mixV T (dec2 n) (dec2 n ∘ permTab (fin24 i)))) a *
        g2 Jl (enc2 (mixV T (dec2 n ∘ permTab (fin24 i)) (dec2 n))) b).sum

theorem qubitAt_of_chk {T : Finset (Fin 4)} {kq : ℕ} {Jl : List (List ℤ)}
    {Fl : List (List (List ℤ))} (h : qubChk T kq Jl Fl = true) : QubitAt T (qF kq Fl) (qJ kq Jl) := by
  intro p
  obtain ⟨i, rfl⟩ := permTab_surj p
  ext a b
  have hab := all_range (all_range (all_range h i.isLt) a.isLt) b.isLt
  simp only [beq_iff_eq, fin24_val] at hab
  have e1 : ((cmap (qJ kq Jl))ᴴ * Osite T (Fin 2) (permTab i) * cmap (qJ kq Jl)) a b =
      ∑ x, ∑ y, (((g2 Jl (enc2 x) a * g2 Jl (enc2 y) b : ℤ) : ℂ)) *
        Osite T (Fin 2) (permTab i) x y := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, qJ, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    push_cast
    simp only [Complex.star_def, map_intCast]
    ring
  rw [e1, sum_Osite, sum_fin42]
  simp only [qF, cmap, Matrix.map_apply, Matrix.of_apply, permIdx_permTab]
  rw [Complex.ofReal_intCast, hab, Int.cast_list_sum, List.map_map]
  simp only [Function.comp_def, Int.cast_mul]

end LayerDT0

#print axioms LayerDT0.sum_Osite
#print axioms LayerDT0.qubitAt_of_chk
