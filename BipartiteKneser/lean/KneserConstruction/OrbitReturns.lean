module

public import KneserConstruction.OrbitLayout
public import KneserConstruction.OrbitZero
public import KneserConstruction.OrbitJoin
public import KneserConstruction.Family

/-! # First omission for the four concrete row families (Proposition 6.5) -/

@[expose] public section

namespace BipartiteKneser.Orbit

open Family Boundary Reduction

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- The bounded checker and the constructor select the same joining table for p. -/
theorem joinCase_boundary (p : ℕ) :
    joinCase (boundaryCase p) = Construction.residueCase p := by
  by_cases he : p % 3 = 1 <;> simp [boundaryCase, joinCase, Construction.residueCase, he]

/-- The first-to-last map comes from the canonical rows, including the replaced
transition at coordinate one. -/
theorem first_last (C : Construction m) (sw : ℕ → Bool) (hc : C.CoversOrders) (χ : ℕ → Bool)
    (parity : ∀ i, ((C.middle i).length % 2 == 0) = !(χ (i.val + 1)))
    (w j : ℕ) (hw : 1 ≤ w) (hwq : w < q) (hj : j < 4) :
    Reach (onFrames (C.complete sw hc))
      (firstFrame (boundaryCase p) m C.special.N C.special.E (slotPoint w j))
      (lastFrame m C.special.K C.special.E (slotPoint w (lastSlot (w - 1) j (χ w) (sw w)))) := by
  let i : Fin (q - 1) := ⟨w - 1, by omega⟩
  have wi : i.val + 1 = w := by dsimp [i]; omega
  let z : Fin 4 := ⟨j, hj⟩
  have za := C.params.index
  have zsize := C.q_eq
  have zero := (zero_rows_paths (C.complete sw hc) C.two_ne za.1 (by omega : C.params.j < C.M)
    C.params.a C.params.b C.v (fun _ h => C.has_zero sw hc h)).1
  have start : decide (i.val = 0) = decide (w = 1) := by simp [← wi]
  have row := (fiberRows_paths (C.complete sw hc) C.two_ne (coord i) (sw (i.val + 1))
    (C.first i) (C.last i) C.params.a C.params.b (C.middle i) (decide (i.val = 0))
    (by intro h; simp only [decide_eq_true_eq] at h; simp [coord, h]) zero
    (fun _ h => C.has_ordinary sw hc i h)).1 (fromSlot z)
  rw [Function.comp_apply, parity, wi, start] at row
  rw [packed_last hw z (χ w) (sw w)]
  rw [← wi, coord_first C i z, coord_last, slot_inverse]
  simpa only [wi] using row

/-- The outgoing map comes from one K-to-N joining row, or the translation splice
at the final fiber. -/
theorem last_first (C : Construction m) (sw : ℕ → Bool) (hc : C.CoversOrders)
    (w j : ℕ) (hw : 1 ≤ w) (hwq : w < q) (hj : j < 4) :
    Reach (onFrames (C.complete sw hc))
      (lastFrame m C.special.K C.special.E (slotPoint w j))
      (firstFrame (boundaryCase p) m C.special.N C.special.E
        (routePoint (boundaryCase p) q w j)) := by
  let z : Fin 4 := ⟨j, hj⟩
  by_cases he : w = q - 1
  · subst w
    have h := (translation_paths (C.complete sw hc) (Translations.paperLayout p C.M C.large)
      C.special.E ((q - 1 : ℕ) : ZMod p) (Translations.w₀ p q) C.two_ne (by omega)
      (fun i => C.has_translation sw hc i)).1 (fromSlot z)
    rw [at_last_w C z, translated_route C z, at_w₀]
    exact h
  · let i : Fin (q - 2) := ⟨w - 1, by omega⟩
    have wi : Joins.number i = (w : ℤ) := by dsimp [Joins.number, i]; omega
    have hq : 65 ≤ q := by have := C.q_eq; have := C.large; omega
    have row : HasRow (C.complete sw hc) (Joins.row m C.special.K C.special.N
        (joinCase (boundaryCase p)) i) := by
      rw [joinCase_boundary]
      exact C.has_join sw hc i
    simpa only [wi] using join_path (C.complete sw hc) C.two_ne (boundaryCase p) hq
      C.special.K C.special.N C.special.E i row z

end BipartiteKneser.Orbit
