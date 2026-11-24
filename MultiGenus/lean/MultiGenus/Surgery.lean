/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySubdivide

/-!
# Inserting an edge in a dart rotation

In `multi_genus.c:add_edge`, the darts `e1` and `e2` are inserted immediately
before `right1` and `right2` in their respective vertex rotations. A face step
is `run->invers->next`: it crosses the edge, then rotates at the destination.
The two equations for new darts and the equation for old darts below specify
this walk on the enlarged dart set. The quotient by these walks counts faces.
-/

@[expose] public section

namespace MultiGenus.Surgery

open Equiv Equiv.Perm

variable {D : Type*}

/-- The old darts together with the two orientations of the inserted edge.
The tags `false` and `true` stand for the C darts `e1` and `e2` respectively. -/
abbrev Inserted (D : Type*) := D ⊕ Bool

/-- Reversal on the enlarged dart set swaps the two new darts. -/
def insertReverse (rev : Perm D) : Perm (Inserted D) := rev.sumCongr (swap false true)

variable [DecidableEq D]

/-- Insert each new dart before the corresponding right dart in the vertex rotation. -/
def insertRotation (rot : Perm D) (a b : D) : Perm (Inserted D) :=
  swap (.inl a) (.inr false) * swap (.inl b) (.inr true) * rot.sumCongr (1 : Perm Bool)

/-- Face permutation after insertion, with `a = right1` and `b = right2`. -/
def insertEdge (p : Perm D) (a b : D) : Perm (Inserted D) :=
  swap (.inl a) (.inr false) * swap (.inl b) (.inr true) * p.sumCongr (swap false true)

/-- Crossing the (possibly new) edge and then rotating gives exactly the insertion permutation. -/
theorem insertRotation_mul_insertReverse (rot rev : Perm D) (a b : D) :
    insertRotation rot a b * insertReverse rev = insertEdge (rot * rev) a b := by
  simp [insertRotation, insertReverse, insertEdge, mul_assoc, sumCongr_mul]

/-- An old walk aiming at `right1` now visits `e1`, one aiming at `right2` visits
`e2`, and every other old step is unchanged. -/
theorem insertEdge_old (p : Perm D) {a b : D} (hab : a ≠ b) (x : D) :
    insertEdge p a b (.inl x) =
      if p x = a then .inr false else if p x = b then .inr true else .inl (p x) := by
  by_cases ha : p x = a
  · simp [insertEdge, Equiv.sumCongr_apply, swap_apply_def, ha, hab]
  by_cases hb : p x = b
  · simp [insertEdge, Equiv.sumCongr_apply, swap_apply_def, hb, hab.symm]
  · simp [insertEdge, Equiv.sumCongr_apply, swap_apply_def, ha, hb]

/-- From `e1` the walk crosses to `e2`, whose rotational successor is `right2`. -/
theorem insertEdge_first (p : Perm D) {a b : D} (hab : a ≠ b) :
    insertEdge p a b (.inr false) = .inl b := by
  simp [insertEdge, Equiv.sumCongr_apply, swap_apply_def, hab.symm]

/-- From `e2` the walk crosses to `e1`, whose rotational successor is `right1`. -/
theorem insertEdge_second (p : Perm D) (a b : D) :
    insertEdge p a b (.inr true) = .inl a := by
  simp [insertEdge, Equiv.sumCongr_apply, swap_apply_def]

/-- Deleting the inserted darts from a facial walk swaps the two old successors.
One compressed step takes two actual steps at a cut and one everywhere else. -/
theorem insertEdge_walk_step (p : Perm D) {a b : D} (hab : a ≠ b) (x : D) :
    (insertEdge p a b ^ (if p x = a ∨ p x = b then 2 else 1 : ℕ)) (.inl x) =
      .inl ((swap a b * p) x) := by
  by_cases ha : p x = a
  · simp [ha, pow_two, insertEdge_old p hab, insertEdge_first p hab]
  by_cases hb : p x = b
  · simp [hb, hab.symm, pow_two, insertEdge_old p hab, insertEdge_second]
  · simp [ha, hb, insertEdge_old p hab, swap_apply_of_ne_of_ne ha hb]

/-- Read a new dart as its next old dart when comparing a full walk to the compressed walk. -/
def collapse (a b : D) : Inserted D → D
  | .inl x => x
  | .inr false => b
  | .inr true => a

/-- The inserted subdivision preserves *exactly* the orbits of the swapped successor
permutation, for arbitrary starting and ending darts, including the new ones. -/
theorem insertEdge_sameCycle_iff [Finite D] (p : Perm D) {a b : D} (hab : a ≠ b)
    (x y : Inserted D) :
    (insertEdge p a b).SameCycle x y ↔
      (swap a b * p).SameCycle (collapse a b x) (collapse a b y) := by
  let g := insertEdge p a b
  let q := swap a b * p
  have proj (z : Inserted D) : q.SameCycle (collapse a b z) (collapse a b (g z)) := by
    cases z with
    | inl d =>
      have he : collapse a b (g (.inl d)) = q d := by
        change collapse a b (insertEdge p a b (.inl d)) = swap a b (p d)
        rw [insertEdge_old p hab]
        split <;> rename_i h
        · simp [collapse, h]
        · split <;> rename_i h'
          · simp [collapse, h']
          · simp [collapse, swap_apply_of_ne_of_ne h h']
      rw [he]
      exact SameCycle.rfl.apply_right
    | inr tag =>
      cases tag
      · change q.SameCycle b (collapse a b (insertEdge p a b (.inr false)))
        rw [insertEdge_first p hab]
        rfl
      · change q.SameCycle a (collapse a b (insertEdge p a b (.inr true)))
        rw [insertEdge_second]
        rfl
  have lift (d : D) : g.SameCycle (.inl d) (.inl (q d)) := by
    let n : ℕ := if p d = a ∨ p d = b then 2 else 1
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact insertEdge_walk_step p hab d⟩
  have retract (z : Inserted D) : g.SameCycle z (.inl (collapse a b z)) := by
    cases z with
    | inl d => exact SameCycle.rfl
    | inr tag =>
      cases tag
      · rw [show Sum.inl (collapse a b (.inr false)) = g (.inr false) from
          (insertEdge_first p hab).symm]
        exact SameCycle.rfl.apply_right
      · rw [show Sum.inl (collapse a b (.inr true)) = g (.inr true) from
          (insertEdge_second p a b).symm]
        exact SameCycle.rfl.apply_right
  exact ⟨map_sameCycle g q _ proj,
    fun h => (retract x).trans ((map_sameCycle q g Sum.inl lift h).trans (retract y).symm)⟩

/-- Collapsing the two subdivision steps gives a bijection of actual face-walk orbits. -/
def faceEquiv [Finite D] (p : Perm D) {a b : D} (hab : a ≠ b) :
    Quotient (SameCycle.setoid (insertEdge p a b)) ≃
      Quotient (SameCycle.setoid (swap a b * p)) where
  toFun := Quotient.map (collapse a b) fun x y => (insertEdge_sameCycle_iff p hab x y).1
  invFun := Quotient.map Sum.inl fun x y => (insertEdge_sameCycle_iff p hab (.inl x) (.inl y)).2
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with | _ x =>
    exact Quotient.sound ((insertEdge_sameCycle_iff p hab _ _).2 SameCycle.rfl)
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with | _ x => rfl

/-- The two new orientations occur on separate new faces in the split case,
and on the same new face in the merge case. -/
theorem insertEdge_new_darts [Finite D] (p : Perm D) {a b : D} (hab : a ≠ b) :
    (insertEdge p a b).SameCycle (.inr false) (.inr true) ↔ ¬ p.SameCycle a b := by
  rw [insertEdge_sameCycle_iff p hab]
  change (swap a b * p).SameCycle b a ↔ _
  rw [sameCycle_comm, sameCycle_swap_mul_endpoints p hab]

/-- Same-face branch of `add_edge`: the number of facial walks increases by one. -/
theorem insertEdge_sameFace [Finite D] (p : Perm D) {a b : D} (hab : a ≠ b)
    (hs : p.SameCycle a b) : countCycles (insertEdge p a b) = countCycles p + 1 :=
  (Nat.card_congr (faceEquiv p hab)).trans (countCycles_swap_mul_same p hab hs)

/-- Different-face branch of `add_edge`: the number of facial walks decreases by one. -/
theorem insertEdge_differentFaces [Finite D] (p : Perm D) {a b : D} (hab : a ≠ b)
    (hd : ¬ p.SameCycle a b) : countCycles (insertEdge p a b) + 1 = countCycles p := by
  calc
    _ = countCycles (swap a b * p) + 1 := congrArg (· + 1) (Nat.card_congr (faceEquiv p hab))
    _ = _ := countCycles_swap_mul_diff p hab hd

end MultiGenus.Surgery
