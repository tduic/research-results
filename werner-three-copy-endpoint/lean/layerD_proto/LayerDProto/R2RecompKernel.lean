import LayerDProto.R2AsmKernel

/-!
# Layer D, (E′): re-presenting a part with full-rank bases (core Lean only)

A part's functional `F(t) = fac · ⟨B_l X B_rᵀ, ⊗_u ρ_u(t_u)⟩` depends on `(k, X, B_l, B_r)` only through
`Y = B_l X B_rᵀ` (`FTP P = FT … (Ymat P.k P.X P.Bl P.Br)`). The fold check `foldBOK` is stated on the
presentation, and the generator can only build its `Q`, `R` when `B_l`, `B_r` have full column rank. In a
coupled block `X` lives on `U ⊕ V` and `B_u = [B_u' 0]`, `B_v = [0 B_v']` never do, so every coupled part is
re-presented (`layerD_proto/recompress.py`) as `Y = L Z Rᵀ` with `L`, `R` of full column rank `r = rank Y`.

The kernel does not trust that re-presentation: `yEqOK` compares the packed rows of both products
(`yRows`, the same packing `partD` uses), with the digit bound `4 |Y_ij| < 2^w` checked on both sides, so the
rows are equal digit by digit (`R2Recomp.lean`: `Ymat_eq_of_yEqOK`). `ycoreOK` adds the fields `FTP` and
`famD` read besides `Y` (`ks`, `fac`, `ρ`).
-/

namespace LayerDProto

/-- `B_l X B_rᵀ = B_l' X' B_r'ᵀ` (as functions of `(i, j)`): same numbers of rows, the shapes, the digit bound
`4 rowsum(B_l) |X| rowsum(B_r) < 2^w` on both sides, and the packed rows equal. -/
def yEqOK (w k : Nat) (X Bl Br : List (List Int)) (k' : Nat) (X' Bl' Br' : List (List Int)) : Bool :=
  Bl'.length == Bl.length && Br'.length == Br.length && decide (0 < w) &&
  isRect k k X && Bl.all (·.length == k) && Br.all (·.length == k) &&
  isRect k' k' X' && Bl'.all (·.length == k') && Br'.all (·.length == k') &&
  decide (4 * (rowSumMax Bl * entMax X * rowSumMax Br) < 2 ^ w) &&
  decide (4 * (rowSumMax Bl' * entMax X' * rowSumMax Br') < 2 ^ w) &&
  yRows k w X Bl Br == yRows k' w X' Bl' Br'

/-- `P'` is a re-presentation of `P`: same `ks`, `fac`, tables, and the same `Y`. -/
def ycoreOK (w : Nat) (P P' : PartData) : Bool :=
  P.ks == P'.ks && P.fac == P'.fac && P.rhos == P'.rhos &&
  yEqOK w P.k P.X P.Bl P.Br P'.k P'.X P'.Bl P'.Br

/-- `P'` has the same core fields as `P` (a `Bool`: `decide` cannot synthesize `DecidableEq` for the
seven-fold product of `PartData.core`). -/
def sameCoreOK (P P' : PartData) : Bool :=
  P.ks == P'.ks && P.k == P'.k && P.X == P'.X && P.Bl == P'.Bl && P.Br == P'.Br && P.fac == P'.fac &&
  P.rhos == P'.rhos

end LayerDProto
