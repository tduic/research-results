import LayerDProto.R2AsmKernel

/-!
# Layer D (t = 0): `partStaticOK` from separate checks (core Lean only)

`partStaticOK` checks the closure of `K` and every fold generator in one declaration; for parts with several
generators the kernel then needs more than 3 GB. `partStaticOK_of` assembles it from the shape and closure check
and one `foldDatumOK` check per generator, each its own declaration in the generated part modules.
-/

namespace LayerDT0

open LayerDProto

theorem partStaticOK_of (bosL : List Nat) (P : PartData)
    (h1 : (P.ks.length == 4 && P.Bl.all (·.length == P.k) && P.Br.all (·.length == P.k) &&
      closureOK bosL (P.folds.map (·.κ)) P.Ks P.tree) = true)
    (h2 : ∀ fd ∈ P.folds, foldDatumOK P fd = true) : partStaticOK bosL P = true := by
  unfold partStaticOK
  rw [h1, List.all_eq_true.2 h2]
  rfl

end LayerDT0

#print axioms LayerDT0.partStaticOK_of
