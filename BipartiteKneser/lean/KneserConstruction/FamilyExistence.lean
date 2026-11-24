module

public import KneserConstruction.Family
public import KneserConstruction.Uniform

/-! # Proposition 5.7 for every prime in the generic range -/

@[expose] public section

namespace BipartiteKneser.Family

/-- The generic prime hypotheses suffice for the concrete row family of Sections 4–5.
One choice of the interior orders works simultaneously for every choice of final signs. -/
theorem exists_complete_family {p q : ℕ} [Fact p.Prime] [NeZero p] [NeZero q]
    (m : Multipliers p q) (size : p = 2 * q + 1) (large : 131 ≤ p) (residue : p % 8 = 3) :
    ∃ C : Construction m, C.CoversOrders ∧ ∀ switch : ℕ → Bool,
      ∃ F : Complete m (C.Row switch), F.row = C.row switch := by
  let M := (q - 1) / 4
  have hM : 16 ≤ M := by dsimp [M]; omega
  have hp : p = 8 * M + 3 := by dsimp [M]; omega
  have hq : q = 4 * M + 1 := by dsimp [M]; omega
  obtain ⟨C, _, hc, _⟩ := exists_construction m hM hp hq
  exact ⟨C, hc, fun switch => ⟨C.complete switch hc, rfl⟩⟩

end BipartiteKneser.Family
