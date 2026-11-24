module

public import KneserConstruction.ReductionLocal
public import KneserConstruction.ReductionIndices

/-! # The symbolic three-strand paths across the ordinary interval -/

@[expose] public section

namespace BipartiteKneser.Reduction

open Boundary Orbit

/-- Address a position in one of the two boundary triples. -/
def addr (minus : Bool) (i : Fin 3) : ℕ := (if minus then 3 else 0) + i.val

/-- The two current entries of the triple, expressed as slots at its coordinate. -/
def currentSlot (minus : Bool) (i : Fin 2) : ℕ :=
  if minus then (if i = 0 then 3 else 1) else (if i = 0 then 0 else 2)

theorem current_point (w : ℤ) (minus : Bool) (i : Fin 2) :
    port w (addr minus i.castSucc) = slotPoint w (currentSlot minus i) := by
  cases minus <;> fin_cases i <;> rfl

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable {m : Multipliers p q} {ι : Type*} {F : Family.Complete m ι} {c : Case}
variable {N E K : Fin q} {χ sw : ℕ → Bool}

/-- The first omission in the coordinates used by the second omission. -/
theorem LocalPaths.first_next (h : LocalPaths c F N E K χ sw) {w j : ℕ}
    (hw : 1 ≤ w) (hq : w < q) (hj : j < 4) :
    Reach (onFrames F) (firstFrame c m N E (slotPoint w j))
      (firstFrame c m N E (routePoint c q w (lastSlot (w - 1) j (χ w) (sw w)))) :=
  (h.first_last w j hw hq hj).trans (h.last_first _ _ hw hq (lastSlot_lt ..))

private theorem ordinary_z (c : Case) {q w : ℕ} (hq : 65 ≤ q)
    (lo : start c ≤ w) (hi : w < stop c q) :
    zValue c q w = (w : ℤ) + 1 ∧ 2 ≤ w ∧ w + 2 < q := by
  rw [stop_eq c hq] at hi
  cases c <;> simp [start, leftCount, count] at lo hi <;>
    simp only [zValue] <;> split_ifs <;> omega

private def target (b : Bool) (i : Fin 2) : Fin 3 :=
  if i = 0 then (if b then 2 else 0) else (if b then 0 else 2)

private theorem ordinary_route (c : Case) {q w : ℕ} (hq : 65 ≤ q)
    (lo : start c ≤ w) (hi : w < stop c q) (missing switch minus : Bool) (i : Fin 2) :
    routePoint c q w (lastSlot (w - 1) (currentSlot minus i) missing switch) =
      port ((w : ℤ) + 1) (addr minus (target (strandSwitch switch missing minus) i)) := by
  obtain ⟨hz, hw, hend⟩ := ordinary_z c hq lo hi
  have no1 : w - 1 ≠ 0 := by omega
  have nolast : (w : ℤ) ≠ (q : ℤ) - 1 := by omega
  have slot (j : ℕ) : lastSlot (w - 1) j missing switch = lastSlot 1 j missing switch := by
    simp only [lastSlot, no1, Nat.one_ne_zero, ite_false]
  rw [slot]
  let j := lastSlot 1 (currentSlot minus i) missing switch
  have flags (b : ℤ) : port b (addr minus (target (strandSwitch switch missing minus) i)) =
      (if j.testBit 1 then b + 1 else b, j.testBit 1 ^^ j.testBit 0, j.testBit 0) := by
    dsimp only [j]
    cases minus <;> cases missing <;> cases switch <;> fin_cases i <;>
      simp +ground [port, addr, target, strandSwitch, currentSlot, lastSlot]
  rw [flags]
  change routePoint c q w j = _
  simp only [routePoint, nolast, ite_false, hz]
  have twice : -((w : ℤ) - 2 * (w + 1)) = w + 2 := by omega
  rw [twice]
  cases h₁ : j.testBit 1 <;> cases h₀ : j.testBit 0 <;>
    simp (disch := omega) [center, ite_eq_left, ite_eq_right, Int.add_assoc] <;> omega

/-- At layer k, slot 2 is already slot 1 of the following layer. -/
noncomputable def layer (c : Case) (m : Multipliers p q) (N E : Fin q) (k : ℕ)
    (minus : Bool) (i : Fin 3) :=
  firstFrame c m N E (port ((start c + k : ℕ) : ℤ) (addr minus i))

theorem interval_step (h : LocalPaths c F N E K χ sw) (hq : 65 ≤ q)
    {k : ℕ} (hk : k < length c q) (minus : Bool) :
    Across (onFrames F) (layer c m N E k minus) (layer c m N E (k + 1) minus)
      (localImage (strandSwitch (sw (start c + k)) (χ (start c + k)) minus)) := by
  let w := start c + k
  have lo : start c ≤ w := Nat.le_add_right ..
  have hi : w < stop c q := by dsimp [stop, w]; omega
  obtain ⟨_, hw, hend⟩ := ordinary_z c hq lo hi
  have two (i : Fin 2) : Reach (onFrames F)
      (layer c m N E k minus i.castSucc)
      (layer c m N E (k + 1) minus (target (strandSwitch (sw w) (χ w) minus) i)) := by
    have hj : currentSlot minus i < 4 := by cases minus <;> fin_cases i <;> decide
    have path := h.first_next (w := w) (by omega) (by omega) hj
    rw [ordinary_route c hq lo hi, ← current_point] at path
    simpa only [layer, Int.add_assoc, Nat.cast_add, Nat.cast_one, w] using path
  apply triple_step
  · exact two 0
  · exact two 1
  · cases minus <;> simp [layer, addr, port, Int.add_assoc]

end BipartiteKneser.Reduction
