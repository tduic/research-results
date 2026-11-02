import LayerDProto.Packed

/-!
# Layer D (t = 0): block multipliers, kernel side (core Lean only)

`BlockPD` is one block's multiplier data from `blocks.jsonl`: `X0` (rows packed in base `2^xb`),
`s`, the margin `μ = mn / 2^me`, the sparse corrections `Δ` (index, numerator over the common
`DEN`), and an untrusted short congruence `W` (packed rows) for `checkPDdd`.

`pdChk`: `X0 − 2^s μ I` passes `checkPDdd` with `W` (so `X0/2^s − μ I ≻ 0`), `me ≤ s`, the
correction indices are in range, and `|Δ_i| / DEN ≤ μ` for every correction.
-/

namespace LayerDT0

open LayerDProto

structure BlockPD where
  k : Nat
  s : Nat
  mn : Nat
  me : Nat
  xb : Nat
  X0p : List Int
  wbits : Nat
  Wp : List Int
  β : Nat
  wb : Nat
  ab : Nat
  eb : Nat
  Δ : List (Nat × Int)

instance : Inhabited BlockPD := ⟨⟨0, 0, 0, 0, 1, [], 1, [], 0, 0, 0, 0, []⟩⟩

def BlockPD.X0 (b : BlockPD) : List (List Int) := b.X0p.map (unpk b.xb b.k)
def BlockPD.W (b : BlockPD) : List (List Int) := b.Wp.map (unpk b.wbits b.k)
def BlockPD.A (b : BlockPD) : List (List Int) := shiftDiag ((b.mn : Int) * 2 ^ (b.s - b.me)) 0 b.X0

def deltaOK (DEN : Nat) (b : BlockPD) : Bool :=
  b.Δ.all fun c => decide (c.1 < b.k) && decide (c.2.natAbs * 2 ^ b.me ≤ b.mn * DEN)

def pdChk (DEN : Nat) (b : BlockPD) : Bool :=
  checkPDdd b.k b.β (2 ^ b.wb) (2 ^ b.ab) (2 ^ b.eb) b.A b.W && decide (b.me ≤ b.s) && deltaOK DEN b

end LayerDT0
