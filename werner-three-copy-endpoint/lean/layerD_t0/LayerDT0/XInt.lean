import LayerDT0.PDCheck

/-!
# Layer D (t = 0): the scaled block multiplier `xint` (core Lean)

`xint DEN pd = X0 · DEN + δ_{pq} Δ_p · 2^s`, i.e. `2^s · DEN · X_b` (`IdentityBlock.ent_xint`, `xint_spec`), as
one walk over the rows of `X0`. It lives in a core-Lean module so that the generated identity modules, which do
not import Mathlib, can name the very same term `xint DEN pdb<j>` as `PsT0`'s parts: the kernel then
identifies the two by unfolding, without computing the matrix (`IdentitySeg.yRel_of_fields`), and computes it
once, in a core-Lean module, against the generated part.
-/

namespace LayerDT0

/-- The correction of diagonal entry `i` (`0` if none); the same function as `PD.deltaAt`. -/
def xdelta (Δ : List (Nat × Int)) (i : Nat) : Int := (Δ.lookup i).getD 0

/-- Row `p` of `xint`, walking the row of `X0` once: entries `q, q+1, …` (`n` of them) of `r · DEN + δ_{pq} dv`. -/
def xrowF (DEN : Nat) (dv : Int) (p : Nat) : Nat → List Int → Nat → List Int
  | _, _, 0 => []
  | q, r, n + 1 => (r.headD 0 * DEN + if p = q then dv else 0) :: xrowF DEN dv p (q + 1) r.tail n

/-- The rows `p, p+1, …` (`n` of them) of `xint`, walking `X0` once. -/
def xrowsF (DEN : Nat) (pd : BlockPD) : Nat → List (List Int) → Nat → List (List Int)
  | _, _, 0 => []
  | p, X, n + 1 => xrowF DEN (xdelta pd.Δ p * 2 ^ pd.s) p 0 (X.headD []) pd.k :: xrowsF DEN pd (p + 1) X.tail n

/-- `c · X_b` as an integer list, `c = 2^s · DEN`: `X0 · DEN + δ_{pq} Δ_p · 2^s`. (An `ent`-indexed definition
costs the kernel `k³` list steps: 4.9 GB for the `k = 74` block.) -/
def xint (DEN : Nat) (pd : BlockPD) : List (List Int) := xrowsF DEN pd 0 pd.X0 pd.k

end LayerDT0
