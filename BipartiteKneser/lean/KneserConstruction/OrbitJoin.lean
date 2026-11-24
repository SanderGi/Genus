import KneserConstruction.FamilyJoins
import KneserConstruction.ReductionLocal

/-! # The K-to-N row in centered boundary coordinates -/

noncomputable section

namespace BipartiteKneser.Orbit

open Boundary Family Coordinates Reduction

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q} {ι : Type*}

/-- Use the same residue case in both the integer join table and the bounded checker. -/
def joinCase : Boundary.Case → FiberJoins.Case
  | .one => .one
  | .two => .two

private theorem center_neg (q x : ℤ) (hq : 0 ≤ q) :
    center q (-x) = -center q x := by unfold center; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
-- Check both output columns on every exceptional row and the two ordinary branches.
private theorem center_targets (c : Boundary.Case) (q w : ℤ) (hq : 65 ≤ q)
    (lo : 1 ≤ w) (hi : w ≤ q - 2) :
    center q (zValue c q w) = FiberJoins.target (joinCase c) q w true ∧
    center q (w - 2 * zValue c q w) = FiberJoins.target (joinCase c) q w false := by
  cases c <;> simp only [joinCase, zValue, FiberJoins.target, FiberJoins.row, ite_true,
    Bool.false_eq_true, ite_false]
  all_goals repeat' split
  all_goals dsimp only
  all_goals unfold center
  all_goals split_ifs <;> omega

/-- Choose the positive fiber and remember the sign of its coordinate. -/
def centeredPoint (k : ℤ) (e : Bool) : Point := (if k < 0 then -k else k, e, decide (k < 0))

omit [NeZero q] in
private theorem missing_name (c : Boundary.Case) :
    FiberJoins.missing (joinCase c) q = if c = .one then 1 else (q : ℤ) - 2 := by cases c <;> rfl

private def output (c : Boundary.Case) (q w : ℤ) (e t : Bool) : ℤ :=
  let z := FiberJoins.target (joinCase c) q w (!e)
  if e ^^ t then -z else z

private theorem route_join (c : Boundary.Case) (q w : ℤ) (hq : 65 ≤ q)
    (lo : 1 ≤ w) (hi : w ≤ q - 2) (j : ℕ) :
    routePoint c q w j = centeredPoint (output c q w (j.testBit 1) (j.testBit 0))
      (j.testBit 1 ^^ j.testBit 0) := by
  obtain ⟨hz, hy⟩ := center_targets c q w hq lo hi
  have ne : w ≠ q - 1 := by omega
  unfold routePoint output
  rw [ite_eq_right ne]
  have hy' : center q (2 * zValue c q w - w) = -FiberJoins.target (joinCase c) q w false := by
    simpa using (center_neg q (w - 2 * zValue c q w) (by omega)).trans (congrArg Neg.neg hy)
  cases j.testBit 1 <;> cases j.testBit 0 <;>
    simp [center_neg q _ (by omega), hz, hy, hy', centeredPoint]

private theorem legal_output (c : Boundary.Case) (q w : ℤ) (hq : 65 ≤ q)
    (lo : 1 ≤ w) (hi : w ≤ q - 2) (e t : Bool) :
    FiberJoins.Required (joinCase c) q (output c q w e t) := by
  have hq' : FiberJoins.InRange (joinCase c) q := by
    cases c <;> simp [joinCase, FiberJoins.InRange] <;> omega
  have ht := (FiberJoins.source_target (joinCase c) hq' lo hi (!e)).1
  unfold output
  split
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ht
    change FiberJoins.Required _ _ (-FiberJoins.target (joinCase c) q w (!e))
    unfold FiberJoins.Required
    omega
  · exact ht

private theorem first_centered {c : Boundary.Case} {k : ℤ}
    (hk : FiberJoins.Required (joinCase c) q k) (e : Bool) (N E : Fin q) :
    firstFrame c m N E (centeredPoint k e) =
      X m (if e then -N else N) (k : ZMod p) := by
  obtain ⟨_, _, _, h₁, h₂⟩ := hk
  rw [missing_name] at h₁ h₂
  by_cases hn : k < 0
  · have hne : -k ≠ (if c = .one then 1 else (q : ℤ) - 2) := by omega
    simp [firstFrame, signedFrame, centeredPoint, hn, hne]
  · simp [firstFrame, signedFrame, centeredPoint, hn, h₁]

/-- The four pass-through paths from an actual joining quadruple. The outgoing
target is a first frame because the missing N-coordinate is excluded by the join table. -/
theorem join_path (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0) (c : Boundary.Case)
    (hq : 65 ≤ q) (K N E : Fin q) (i : Fin (q - 2))
    (row : HasRow F (Joins.row m K N (joinCase c) i)) (j : Fin 4) :
    let w := Joins.number i
    Reach (onFrames F) (lastFrame m K E (slotPoint w j.val))
      (firstFrame c m N E (routePoint c q w j.val)) := by
  let w := Joins.number i
  have lo : 1 ≤ w := by dsimp [w, Joins.number]; omega
  have hi : w ≤ (q : ℤ) - 2 := by dsimp [w, Joins.number]; have := i.isLt; omega
  have ne : w ≠ (q : ℤ) - 1 := by omega
  change Reach _ (lastFrame _ _ _ (slotPoint w _)) (firstFrame _ _ _ _ (routePoint _ _ w _))
  rw [route_join c q w (by omega) lo hi, first_centered (legal_output c q w (by omega) lo hi _ _)]
  apply Reach.step
  have hf := row.assign
  fin_cases j
  · simpa +ground [lastFrame, signedFrame, slotPoint, ne, output, Joins.row, w, Quad.dom, Quad.ran]
      using hf (false, false)
  · simpa +ground [lastFrame, signedFrame, slotPoint, ne, output, Joins.row, w, Quad.dom, Quad.ran,
      inverse_X' m h2] using hf (true, false)
  · simpa +ground [lastFrame, signedFrame, slotPoint, ne, output, Joins.row, w, Quad.dom, Quad.ran,
      inverse_X' m h2] using hf (true, true)
  · simpa +ground [lastFrame, signedFrame, slotPoint, ne, output, Joins.row, w, Quad.dom, Quad.ran,
      inverse_X' m h2] using hf (false, true)

omit [NeZero q] in
/-- Convert the coordinate output into a legal first-frame slot for global drainage. -/
theorem route_legal (c : Boundary.Case) (hq : 65 ≤ q) {w : ℕ} (hw : 1 ≤ w) (h : w < q)
    (j : ℕ) : ∃ w' : ℕ, 1 ≤ w' ∧ w' < q ∧ ∃ j' : Fin 4,
      routePoint c q w j = slotPoint w' j'.val := by
  have slots (e t : Bool) : ∃ i : Fin 4, i.val.testBit 1 = e ∧ i.val.testBit 0 = t := by
    revert e t; decide
  suffices H : 1 ≤ (routePoint c q w j).1 ∧ (routePoint c q w j).1 < q by
    let x := routePoint c q w j
    obtain ⟨i, he, ht⟩ := slots x.2.1 x.2.2
    refine ⟨x.1.toNat, by dsimp [x]; omega, by dsimp [x]; omega, i, ?_⟩
    change x = slotPoint _ _
    rw [Int.toNat_of_nonneg (show 0 ≤ x.1 by dsimp [x]; omega)]
    exact Prod.ext rfl (Prod.ext he.symm ht.symm)
  by_cases he : (w : ℤ) = (q : ℤ) - 1
  · cases c <;> simp [routePoint, he] <;> omega
  · rw [route_join c q w (by omega) (by omega) (by omega)]
    have ⟨h₁, h₂, h₃, _, _⟩ := legal_output c q w (by omega) (by omega) (by omega)
      (j.testBit 1) (j.testBit 0)
    unfold centeredPoint
    split <;> dsimp only <;> omega

end BipartiteKneser.Orbit
