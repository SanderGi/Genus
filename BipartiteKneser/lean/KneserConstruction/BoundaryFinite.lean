import KneserConstruction.BoundaryData

/-! The two intervals of checked character masks cover all formal patterns. -/

namespace BipartiteKneser.Boundary

theorem check_all (c : Case) (chars : Pattern c) : ∃ v, check c chars v = true := by
  have covered : Covered c 0 (2 ^ count c) := by
    cases c
    · exact one_covered
    · exact two_covered
  simpa [Fin.ofNat, Nat.mod_eq_of_lt chars.isLt] using covered chars

end BipartiteKneser.Boundary
