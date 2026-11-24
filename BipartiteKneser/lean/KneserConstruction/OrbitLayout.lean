module

public import KneserConstruction.OrbitFiber
public import KneserConstruction.FamilyConstruction
public import KneserConstruction.OrbitTranslation

/-! # Relabeling the positive fibers and the translation ports -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Orbit

open Family Coordinates Reduction Boundary

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- Residue case in the normalized finite witness. -/
def boundaryCase (p : ℕ) : Boundary.Case := if p % 3 = 1 then .one else .two

/-- The first frame at coordinate i + 1 is the indicated slot of the constructor’s first exponent
pair. -/
theorem coord_first (C : Construction m) (i : Fin (q - 1)) (j : Fin 4) :
    firstFrame (boundaryCase p) m C.special.N C.special.E (slotPoint (i.val + 1 : ℕ) j.val) =
      fiber m (C.first i) (coord i) (fromSlot j) := by
  have name : FiberJoins.missing (Construction.residueCase p) q =
      (if boundaryCase p = .one then 1 else (q : ℤ) - 2) := by
    by_cases h : p % 3 = 1 <;> simp [Construction.residueCase, FiberJoins.missing, boundaryCase, h]
  unfold firstFrame
  rw [signed_slot C.two_ne]
  simp [Construction.first, firstExp, coord, slotPoint, name]

/-- The last frame at coordinate i + 1 is the indicated slot of the constructor’s final exponent
pair. -/
theorem coord_last (C : Construction m) (i : Fin (q - 1)) (j : Fin 4) :
    lastFrame m C.special.K C.special.E (slotPoint (i.val + 1 : ℕ) j.val) =
      fiber m (C.last i) (coord i) (fromSlot j) := by
  have hq := C.q_eq
  unfold lastFrame
  rw [signed_slot C.two_ne]
  have cast : ((i.val + 1 : ℕ) : ℤ) = (q : ℤ) - 1 ↔ i.val + 1 = q - 1 := by omega
  simp only [slotPoint, Construction.last, lastExp, coord, cast, Int.cast_natCast]

/-- The translation splice returns to a positive fiber strictly below q. -/
theorem w₀_bounds (C : Construction m) :
    1 ≤ Translations.w₀ p q ∧ Translations.w₀ p q < q := by
  have := C.q_eq
  have := C.large
  unfold Translations.w₀
  split <;> omega

private theorem w₀_name (C : Construction m) :
    ((Translations.w₀ p q : ℕ) : ℤ) =
      (if boundaryCase p = .one then 1 else (q : ℤ) - 2) := by
  have := C.q_eq
  have := C.large
  by_cases h : p % 3 = 1 <;> simp [Translations.w₀, boundaryCase, h]; omega

/-- Identify the four translation exits with the initial E slots at the attachment coordinate. -/
theorem at_w₀ (C : Construction m) (i : Fin 4) :
    firstFrame (boundaryCase p) m C.special.N C.special.E
      (slotPoint (Translations.w₀ p q) (toSlot i).val) =
        fiber m C.special.E (Translations.w₀ p q) i := by
  unfold firstFrame
  simp only [slotPoint, ← w₀_name C, ite_true]
  exact (signed_slot C.two_ne C.special.E (Translations.w₀ p q) (toSlot i)).trans
    (by rw [slot_inverse]; simp)

/-- At coordinate q − 1 the boundary route lands at the translation attachment with the slot given
by the splice. -/
theorem translated_route (C : Construction m) (i : Fin 4) :
    routePoint (boundaryCase p) q (q - 1 : ℕ) i.val =
      slotPoint (Translations.w₀ p q) (toSlot (Splice.translationExit (fromSlot i))).val := by
  have he : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := C.q_eq; omega
  unfold routePoint
  simp only [he, ite_true, ← w₀_name C]
  fin_cases i <;> rfl

/-- The four slots of the final pair at coordinate q − 1 have exponent pair ±E. -/
theorem at_last_w (C : Construction m) (i : Fin 4) :
    lastFrame m C.special.K C.special.E (slotPoint (q - 1 : ℕ) i.val) =
      fiber m C.special.E ((q - 1 : ℕ) : ZMod p) (fromSlot i) := by
  have he : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := C.q_eq; omega
  unfold lastFrame
  simp only [slotPoint, he, ite_true]
  simpa only [← he, slotPoint, Int.cast_natCast] using
    (signed_slot C.two_ne C.special.E ((q - 1 : ℕ) : ℤ) i)

end BipartiteKneser.Orbit
