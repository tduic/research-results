import LayerDProto.R2AsmKernel

/-!
# Layer D (t = 0): `familyZeroOK` from per-part bounds (core Lean)

`familyZeroOK β parts` evaluates `Fbound` of every part of the family in one declaration (`famBound`). That is
cheap for small parts but not for large ones (block 496, `k = 58`: 136 s and 0.3 GB for its `Fbound` alone), and
the family declaration would add them all up. The generated part module checks `fb<i> : Fbound P<i> ≤ b_i` with a
literal `b_i`, and the family module only adds the literals:

* `famBoundB parts bs`: `famBound` with `Fbound` replaced by the bounds `bs`;
* `famBound_le`: `famBound parts ≤ famBoundB parts bs` when `Fbound x.1 ≤ b` part by part;
* **`familyZeroOK_of_bounds`**.
-/

namespace LayerDT0

open LayerDProto

/-- `famBound` with the parts' `Fbound` replaced by the bounds `bs`. -/
def famBoundB (parts : List (PartData × PartAtD)) (bs : List Nat) : Nat :=
  ((parts.zip bs).map fun x => x.1.1.fac.natAbs * x.1.1.Ks.length * x.1.2.reps.length * x.2).foldl (· + ·) 0

/-- `Fbound x.1 ≤ b` part by part (core Lean has no `List.Forall₂`). -/
inductive FbLe : List (PartData × PartAtD) → List Nat → Prop
  | nil : FbLe [] []
  | cons {x : PartData × PartAtD} {b : Nat} {xs : List (PartData × PartAtD)} {bs : List Nat} :
      Fbound x.1 ≤ b → FbLe xs bs → FbLe (x :: xs) (b :: bs)

theorem famBound_le_aux : ∀ (parts : List (PartData × PartAtD)) (bs : List Nat), FbLe parts bs →
    ∀ a a', a ≤ a' →
      (parts.map fun x => x.1.fac.natAbs * x.1.Ks.length * x.2.reps.length * Fbound x.1).foldl (· + ·) a ≤
        ((parts.zip bs).map fun x => x.1.1.fac.natAbs * x.1.1.Ks.length * x.1.2.reps.length * x.2).foldl (· + ·) a'
  | [], [], FbLe.nil, a, a', h => by simpa using h
  | x :: xs, b :: bs, FbLe.cons hb h, a, a', ha => by
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    exact famBound_le_aux xs bs h _ _ (Nat.add_le_add ha (Nat.mul_le_mul_left _ hb))

theorem famBound_le (parts : List (PartData × PartAtD)) (bs : List Nat) (h : FbLe parts bs) :
    famBound parts ≤ famBoundB parts bs :=
  famBound_le_aux parts bs h 0 0 (Nat.le_refl 0)

/-- **`familyZeroOK` from per-part bounds.** -/
theorem familyZeroOK_of_bounds (β : Nat) (parts : List (PartData × PartAtD)) (bs : List Nat) (h : FbLe parts bs)
    (hz : (famTotal parts == 0 && decide (4 * famBoundB parts bs < 2 ^ β)) = true) :
    familyZeroOK β parts = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
  simp only [familyZeroOK, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hz.1, Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 4 (famBound_le parts bs h)) hz.2⟩

end LayerDT0

#print axioms LayerDT0.familyZeroOK_of_bounds
