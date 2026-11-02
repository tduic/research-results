import LayerDT0.Gen.Endpoint
import LayerDT0.Gen.IdentityParts
import LayerDT0.Gen.Id.F31.Core
import LayerDT0.Gen.Id.F22.Core
import LayerDT0.Gen.Id.F13.Core

/-! # The three-copy Werner endpoint in every dimension, unconditionally

`IdentityT0` (the certificate identity, layer D obligation 7) from the three per-family zero checks, and with it
the final theorem: for every local dimension `d` and every operator `C` on `(ℂ^d)^{⊗3}` of rank at most two,
`q(C) = ∑_S (−1/2)^{|S|} ‖Tr_S C‖²_F ≥ 0`.

This module imports the generated `Gen/Id/F<f>/Core` modules, so it builds only after every module of
`identity_modules.txt` has been kernel-checked (`run_identity.sh` and `run_full.sh`; see `README.md`). It is not a default target. -/

namespace LayerDT0

/-- **The certificate identity**, from the family zero checks of the three moment families
(`Fam` is `f31 | f22 | f13`). -/
theorem identityT0 : IdentityT0 :=
  identityT0_of_famZero (fun f => by
    cases f
    exacts [Gen.Id.F31.famZeroT0, Gen.Id.F22.famZeroT0, Gen.Id.F13.famZeroT0])

/-- **The three-copy Werner endpoint in every dimension**: `q(C) ≥ 0` for every `d` and every `C` of rank `≤ 2`. -/
theorem werner3_endpoint_all_d :
    ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ WernerEndpoint.qfun C :=
  werner3_endpoint_all_d_of_identityT0 identityT0

end LayerDT0

#print axioms LayerDT0.identityT0
#print axioms LayerDT0.werner3_endpoint_all_d
