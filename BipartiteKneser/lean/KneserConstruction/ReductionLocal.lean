module

public import KneserConstruction.BoundaryCoordinates
public import KneserConstruction.OrbitRows

/-! # Local paths used by the global orbit reduction -/

@[expose] public section

namespace BipartiteKneser.Reduction

open Boundary Family Coordinates Orbit

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Use the two flags of a point to sign its exponent and coordinate. -/
noncomputable def signedFrame (m : Multipliers p q) (k : Fin q) (x : Point) : Frame p q :=
  X m (if x.2.1 then -k else k) (if x.2.2 then -(x.1 : ZMod p) else (x.1 : ZMod p))

/-- The first exponent is E at the translation attachment and N elsewhere. -/
noncomputable def firstFrame (c : Case) (m : Multipliers p q) (N E : Fin q) (x : Point) :
    Frame p q :=
  signedFrame m (if x.1 = (if c = .one then 1 else (q : ℤ) - 2) then E else N) x

/-- The last exponent is E at the final positive coordinate and K elsewhere. -/
noncomputable def lastFrame (m : Multipliers p q) (K E : Fin q) (x : Point) : Frame p q :=
  signedFrame m (if x.1 = (q : ℤ) - 1 then E else K) x

/-- Read a slot in the boundary order (++), (+−), (−+), (−−). -/
def slotPoint (w : ℤ) (j : ℕ) : Point := (w, j.testBit 1, j.testBit 0)

/-- The row-level facts from the first omission. All switches use the actual
positive coordinate as their argument, including the one at fiber 1. -/
structure LocalPaths {m : Multipliers p q} {ι : Type*} (c : Case) (F : Complete m ι)
    (N E K : Fin q) (χ switch : ℕ → Bool) : Prop where
  first_last (w j : ℕ) (hw : 1 ≤ w) (hq : w < q) (hj : j < 4) :
    Reach (onFrames F) (firstFrame c m N E (slotPoint w j))
      (lastFrame m K E (slotPoint w (lastSlot (w - 1) j (χ w) (switch w))))
  last_first (w j : ℕ) (hw : 1 ≤ w) (hq : w < q) (hj : j < 4) :
    Reach (onFrames F) (lastFrame m K E (slotPoint w j))
      (firstFrame c m N E (routePoint c q w j))
  drain (x : Family.Label m) : ∃ w : ℕ, 1 ≤ w ∧ w < q ∧ ∃ j : Fin 4,
    Reach (onFrames F) x.val (firstFrame c m N E (slotPoint w j))

end BipartiteKneser.Reduction
