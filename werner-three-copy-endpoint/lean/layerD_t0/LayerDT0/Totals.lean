import LayerDT0.IdentityAsm
import LayerDProto.R2Reduced

/-!
# Layer D (t = 0): the literal-free family totals, interface lemmas

The generated family modules (`layerD_t0/gen_totals.py`, `Gen/Id/F<f>/Fam.lean`) prove
`famZero : FamZero f Ps` for their part list `Ps` through the reduced-grid checks
(`LayerDProto.family_at_d_zeroR`, then `famZero_of_grid`). This file adds what step 1 (the decomposition
`hdec` of `identity_of_decomp`) needs to use them with its own part list:

* `famReduced`: `famZero_of_grid` with `hzero` supplied grid value by grid value from `family_at_d_zeroR`
  (the statement the generated `Fam.lean` instantiates);
* `famZero_congr`: `FamZero` only depends on each part's `(ks, k, X, B_l, B_r, fac, ρ)` (`PartData.core`),
  not on its fold data, `K`, tree, widths or bounds. So if step 1's `Ps f` and the generated list have the
  same cores (one `decide`/`rfl`), the generated `famZero` is step 1's `FamZero f (Ps f)`.
-/

open Finset

namespace LayerDT0

open WernerEndpoint LayerDProto

/-- The fields of a part that its functional `fac · FTP` depends on. -/
def PartData.core (P : PartData) :
    List ℕ × ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × ℤ × List (List (List (List ℤ))) :=
  (P.ks, P.k, P.X, P.Bl, P.Br, P.fac, P.rhos)

theorem famD_congr {Ps Ps' : List PartData} (h : Ps.map PartData.core = Ps'.map PartData.core) :
    famD Ps = famD Ps' := by
  funext t
  set g : List ℕ × ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × ℤ × List (List (List (List ℤ))) → ℤ :=
    fun c => c.2.2.2.2.2.1 * FT (nth c.1 0 1) (nth c.1 1 1) (nth c.1 2 1) (nth c.1 3 1) c.2.2.2.2.2.2
      (Ymat c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1) t
  have e : ∀ L : List PartData, (L.map fun P => P.fac * FTP P t) = (L.map PartData.core).map g := by
    intro L; rw [List.map_map]; rfl
  unfold famD
  rw [e, e, h]

/-- **`FamZero` depends only on the parts' cores.** -/
theorem famZero_congr {f : Fam} {Ps Ps' : List PartData} (h : Ps.map PartData.core = Ps'.map PartData.core)
    (hz : FamZero f Ps) : FamZero f Ps' := by
  intro x h1 h2 h3 h4
  rw [← famD_congr h]
  exact hz x h1 h2 h3 h4

/-- **`FamZero` from the reduced checks of every grid value.** `hR d` is `family_at_d_zeroR`'s conclusion at
grid value `d` for the grid `S1 = (s1 d).map Fin.val`. -/
theorem famReduced {f : Fam} (Ps : List PartData) (bosF dc : List (Fin 24)) (s1 : Fin 24 → List (Fin 24))
    (hbosF : ∀ g ∈ bosF, permTab g ∈ bos f) (hmeets : meetsR bosF dc s1 = true)
    (hR : ∀ dd ∈ dc, ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < ((s1 dd).map Fin.val).length,
      ∑ p : PF f, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt ((s1 dd).map Fin.val) dd t0 t1 i2))).sum = 0) :
    FamZero f Ps :=
  famZero_of_grid Ps bosF dc s1 hbosF hmeets fun dd hdd t0 ht0 t1 ht1 i2 hi2 =>
    hR dd hdd t0 ht0 t1 ht1 i2 (by rw [List.length_map]; exact hi2)

end LayerDT0

#print axioms LayerDT0.famZero_congr
#print axioms LayerDT0.famReduced
