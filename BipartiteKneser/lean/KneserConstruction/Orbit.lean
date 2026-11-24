import KneserConstruction.FamilyDrain
import KneserConstruction.OrbitReturns
import KneserConstruction.Reduction

/-! # From generic quadruples and a boundary witness to one local rotation cycle

The family is assembled anew for the switches extracted from the interval witness.
Every retained edge lifts along the actual assignments of its quadruples, and every
connection label occurs in a row whose source reaches a retained vertex. -/

namespace BipartiteKneser.Orbit

open Family Reduction

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- Both first-return diagrams and exhaustion of the original connection set. -/
theorem localPaths (C : Construction m) (sw : ℕ → Bool) (hc : C.CoversOrders) {χ : ℕ → Bool}
    (parity : ∀ i, ((C.middle i).length % 2 == 0) = !(χ (i.val + 1))) :
    LocalPaths (boundaryCase p) (C.complete sw hc) C.special.N C.special.E C.special.K χ sw :=
  ⟨first_last C sw hc χ parity, last_first C sw hc, FamilyDrain.drain C sw hc (last_first C sw hc)⟩

/-- Apply the checked finite certificate to the generic complete family. -/
theorem exists_oneCycle (C : Construction m) (hc : C.CoversOrders)
    (parity : ∀ i, ((C.middle i).length % 2 == 0) = !(Coordinates.missingBit p (i.val + 1))) :
    ∃ sw : ℕ → Bool, OneCycle (C.complete sw hc).rho :=
  Reduction.exists_complete_oneCycle C hc (fun sw => localPaths C sw hc parity)

end BipartiteKneser.Orbit
