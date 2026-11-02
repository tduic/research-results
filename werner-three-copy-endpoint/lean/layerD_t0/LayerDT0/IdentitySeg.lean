import LayerDT0.IdentityDec
import LayerDT0.IdentityFin
import LayerDT0.Recomp

/-!
# Layer D (t = 0): `psOf allParts` as a concatenation of short segments

The generated part lists are compared with `psOf (allParts …) f` part by part (`yr<i>`). Read off
`allParts` directly, the kernel walks the whole list up to part `i`, and `allParts` indexes the blocks and rows
with `getD` (a quadratic walk): one core check of a late part cost 3.1–5.3 GB. This file rewrites
`psOf (allParts …) f` as `segO ++ segB L₀ ++ … ++ segR R₀ ++ …` for any splitting of the block list
`bcs.zip pds` into `L₀ ++ L₁ ++ …` and of the row list `codes.zip num` into `R₀ ++ …`, so each core check only
walks its own segment (`Gen/IdentityParts.lean`: `PsT0` is defined as this concatenation, `PsT0_eq`).

* `range_flatMap_getD`: `(range n).flatMap (fun j => F (as.getD j _) (bs.getD j _)) = (as.zip bs).flatMap …`.
* `allParts_zip`, `psOf_append`, `psOf_flatMap`, **`psOf_allParts_seg`**.
* `forall2_append`: `Forall₂` of concatenations, for the segment-wise core relation.
-/

namespace LayerDT0

open WernerEndpoint LayerDProto

/-- A row's tagged parts for a given multiplier numerator `v` (`rowParts` with `num.getD r 0 = v`). -/
def rowPartsV (S : ℕ) (v : ℤ) (den : ℕ) (c : RowCode) : List (Fam × PartData) :=
  c.uterms.map fun u => (u.f, unitPart (u.coef * v * ((S / den : ℕ) : ℤ)) u.j u.a)

theorem rowParts_eq (S : ℕ) (num : List ℤ) (den r : ℕ) (c : RowCode) :
    rowParts S num den r c = rowPartsV S (num.getD r 0) den c := rfl

/-- The objective segment of family `f`. -/
def segO (S : ℕ) (f : Fam) : List PartData := psOf (objParts S) f

/-- The parts of family `f` of a list of blocks (block code, multiplier). -/
def segB (cuts : ℕ → CutData) (DEN S : ℕ) (f : Fam) (L : List (BCode × BlockPD)) : List PartData :=
  L.flatMap fun x => psOf (blockParts cuts DEN S x.1 x.2) f

/-- The parts of family `f` of a list of rows (row code, multiplier numerator). -/
def segR (S den : ℕ) (f : Fam) (L : List (RowCode × ℤ)) : List PartData :=
  L.flatMap fun x => psOf (rowPartsV S x.2 den x.1) f

theorem range_flatMap_getD {α β γ : Type} (F : α → β → List γ) (da : α) (db : β) :
    ∀ (as : List α) (bs : List β) (n : ℕ), as.length = n → bs.length = n →
      (List.range n).flatMap (fun j => F (as.getD j da) (bs.getD j db)) = (as.zip bs).flatMap fun x => F x.1 x.2
  | [], _, n, ha, _ => by subst ha; simp
  | _ :: _, [], n, ha, hb => by subst hb; simp at ha
  | a :: as, b :: bs, n, ha, hb => by
    subst ha
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hb
    have ih := range_flatMap_getD F da db as bs as.length rfl hb
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.zip_cons_cons, List.flatMap_cons, ← ih]
    simp [List.flatMap_map]

theorem allParts_zip (cuts : ℕ → CutData) (DEN S nb : ℕ) (bcs : List BCode) (pds : List BlockPD) (nr : ℕ)
    (codes : List RowCode) (num : List ℤ) (den : ℕ) (hb : bcs.length = nb) (hp : pds.length = nb)
    (hc : codes.length = nr) (hn : num.length = nr) :
    allParts cuts DEN S nb bcs pds nr codes num den =
      objParts S ++ (bcs.zip pds).flatMap (fun x => blockParts cuts DEN S x.1 x.2) ++
        (codes.zip num).flatMap (fun x => rowPartsV S x.2 den x.1) := by
  unfold allParts
  rw [range_flatMap_getD (blockParts cuts DEN S) default default bcs pds nb hb hp]
  have : ∀ r, rowParts S num den r (rowAt codes r) = rowPartsV S (num.getD r 0) den (codes.getD r .trace) :=
    fun _ => rfl
  simp only [this]
  rw [range_flatMap_getD (fun c v => rowPartsV S v den c) RowCode.trace 0 codes num nr hc hn]

theorem psOf_append (L L' : List (Fam × PartData)) (f : Fam) : psOf (L ++ L') f = psOf L f ++ psOf L' f := by
  simp [psOf, List.filter_append, List.map_append]

theorem psOf_flatMap {α : Type} (L : List α) (F : α → List (Fam × PartData)) (f : Fam) :
    psOf (L.flatMap F) f = L.flatMap fun x => psOf (F x) f := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, psOf_append, ih, List.flatMap_cons]

/-- **The segment form.** For any splitting `bcs.zip pds = LB` and `codes.zip num = LR`,
`psOf (allParts …) f = segO ++ segB LB ++ segR LR` (and `segB`, `segR` split along `++`, `segB_append`). -/
theorem psOf_allParts_seg (cuts : ℕ → CutData) (DEN S nb : ℕ) (bcs : List BCode) (pds : List BlockPD) (nr : ℕ)
    (codes : List RowCode) (num : List ℤ) (den : ℕ) (hb : bcs.length = nb) (hp : pds.length = nb)
    (hc : codes.length = nr) (hn : num.length = nr) (LB : List (BCode × BlockPD)) (LR : List (RowCode × ℤ))
    (hLB : bcs.zip pds = LB) (hLR : codes.zip num = LR) (f : Fam) :
    psOf (allParts cuts DEN S nb bcs pds nr codes num den) f =
      segO S f ++ segB cuts DEN S f LB ++ segR S den f LR := by
  rw [allParts_zip cuts DEN S nb bcs pds nr codes num den hb hp hc hn, psOf_append, psOf_append, psOf_flatMap,
    psOf_flatMap, hLB, hLR]
  rfl

theorem segB_append (cuts : ℕ → CutData) (DEN S : ℕ) (f : Fam) (L L' : List (BCode × BlockPD)) :
    segB cuts DEN S f (L ++ L') = segB cuts DEN S f L ++ segB cuts DEN S f L' := List.flatMap_append

theorem segR_append (S den : ℕ) (f : Fam) (L L' : List (RowCode × ℤ)) :
    segR S den f (L ++ L') = segR S den f L ++ segR S den f L' := List.flatMap_append

/-- `Forall₂` of concatenations (for the segment-wise core relation of the generated `Core.lean`). -/
theorem forall2_append {R : PartData → PartData → Prop} {a b c d : List PartData} (h1 : List.Forall₂ R a c)
    (h2 : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact List.Forall₂.cons h ih

/-- **Field-wise core relation** for the generated core checks of the block parts: the small fields by a
`Bool` check (`decide +kernel`), `X`, `B_l`, `B_r` as equalities that the kernel sees by unfolding (`rfl`): the
generated part writes `X` as the same term `xint DEN pdb<j>` (`XInt.lean`, core Lean) and the bases as the block
code's own packed rows, so nothing is computed here; the generated core-Lean module computes them once. -/
theorem yRel_of_fields {P Q : PartData} (h : (P.ks == Q.ks && P.k == Q.k && P.fac == Q.fac && P.rhos == Q.rhos) = true)
    (hx : P.X = Q.X) (hl : P.Bl = Q.Bl) (hr : P.Br = Q.Br) : YRel P Q := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h6⟩, h7⟩ := h
  exact yRel_of_core (by simp only [PartData.core, h1, h2, hx, hl, hr, h6, h7])

end LayerDT0

#print axioms LayerDT0.psOf_allParts_seg
#print axioms LayerDT0.forall2_append
#print axioms LayerDT0.segB_append
#print axioms LayerDT0.yRel_of_fields
