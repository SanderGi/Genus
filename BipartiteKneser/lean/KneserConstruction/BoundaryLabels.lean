import KneserConstruction.BoundaryCoordinates

/-! Large-q boundary labels are pairwise distinct. -/

namespace BipartiteKneser.Boundary

/-- Only the high-end fibers move when q increases. -/
private def shiftPoint (q : Int) (v : Point) : Point :=
  (if v.1 ≤ 6 then v.1 else v.1 + (q - 65), v.2)

private theorem decode_shift (c : Case) (q : Int) (x : Label c) :
    decode c q x = shiftPoint q (decode c 65 x) := by
  have n : count c ≤ 14 := by cases c <;> decide
  have l : leftCount c ≤ 4 := by cases c <;> decide
  unfold decode
  split <;> rename_i h
  · unfold outside
    split <;> rename_i hi <;>
      simp (disch := omega) [shiftPoint, ite_eq_left, ite_eq_right]
  · simp only [port, shiftPoint]
    split <;> simp (disch := omega) [ite_eq_left]

/-- The 54 or 62 labels decode to distinct symbolic coordinates throughout the large-q range. -/
theorem decode_injective (c : Case) (q : Int) (hq : 65 ≤ q) : Function.Injective (decode c q) := by
  have at65 : Function.Injective (decode c 65) := by
    cases c <;> unfold Function.Injective <;> decide +kernel
  intro x y h
  rw [decode_shift c q x, decode_shift c q y] at h
  apply at65
  generalize decode c 65 x = X at h ⊢
  generalize decode c 65 y = Y at h ⊢
  obtain ⟨a, u⟩ := X
  obtain ⟨b, v⟩ := Y
  change (if a ≤ 6 then a else a + (q - 65), u) = (if b ≤ 6 then b else b + (q - 65), v) at h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  congr 1
  · split at h₁ <;> split at h₁ <;> omega

end BipartiteKneser.Boundary
