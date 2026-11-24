/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySwap
public import Mathlib.GroupTheory.Perm.Option

/-!
# Subdividing and suppressing a facial step

Inserting `none` before a specified dart adds one step to its facial walk.
Suppressing a dart that is not a singleton reverses this operation.
-/

@[expose] public section

namespace MultiGenus.Surgery

open Equiv Equiv.Perm

variable {D E : Type*}

/-- An equivalence intertwining dart successors preserves their face count. -/
theorem countCycles_congr [Finite D] [Finite E] (e : D ≃ E) (p : Perm D) (q : Perm E)
    (h : ∀ x, e (p x) = q (e x)) : countCycles p = countCycles q := by
  apply Nat.card_congr (Quotient.congr e ?_)
  intro x y
  change p.SameCycle x y ↔ q.SameCycle (e x) (e y)
  constructor
  · exact map_sameCycle p q e (fun z => by rw [h]; exact SameCycle.rfl.apply_right)
  · intro same
    have back (z : E) : p.SameCycle (e.symm z) (e.symm (q z)) := by
      rw [← e.apply_symm_apply z, ← h, e.symm_apply_apply, e.symm_apply_apply]
      exact SameCycle.rfl.apply_right
    simpa using map_sameCycle q p e.symm back same

/-- A retraction between the two dart sets induces an equivalence of orbit quotients
if steps lift to walks in both directions and retracting stays within each orbit. -/
def quotientEquivOfRetraction [Finite D] [Finite E] (p : Perm D) (q : Perm E)
    (expand : D → E) (project : E → D) (retract : Function.LeftInverse project expand)
    (oldStep : ∀ d, q.SameCycle (expand d) (expand (p d)))
    (newStep : ∀ z, p.SameCycle (project z) (project (q z)))
    (returns : ∀ z, q.SameCycle (expand (project z)) z) :
    Quotient (SameCycle.setoid q) ≃ Quotient (SameCycle.setoid p) where
  toFun := Quotient.map project fun _ _ => map_sameCycle q p project newStep
  invFun := Quotient.map expand fun _ _ => map_sameCycle p q expand oldStep
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with | _ x => exact Quotient.sound (returns x)
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (retract x)

section

variable [DecidableEq D]

/-- Insert one fresh dart immediately before dart `a` on its face walk. -/
def subdivideBefore (p : Perm D) (a : D) : Perm (Option D) := swap none (some a) * p.optionCongr

/-- The new dart takes one step to the old target. -/
@[simp] theorem subdivideBefore_none (p : Perm D) (a : D) :
    subdivideBefore p a none = some a := by simp [subdivideBefore]

/-- Only the old predecessor of the cut enters the new dart. -/
theorem subdivideBefore_some (p : Perm D) (a x : D) :
    subdivideBefore p a (some x) = if p x = a then none else some (p x) := by
  by_cases h : p x = a <;> simp [subdivideBefore, swap_apply_def, h]

/-- Subdivision replaces one step by two and preserves the number of faces. -/
theorem countCycles_subdivideBefore [Finite D] (p : Perm D) (a : D) :
    countCycles (subdivideBefore p a) = countCycles p := by
  let q := subdivideBefore p a
  let project (z : Option D) := z.getD a
  have oldStep (d : D) : q.SameCycle (some d) (some (p d)) := by
    have edge := (SameCycle.refl q (some d)).apply_right
    change q.SameCycle (some d) (subdivideBefore p a (some d)) at edge
    rw [subdivideBefore_some] at edge
    split at edge <;> rename_i h
    · rw [h, ← subdivideBefore_none p a]
      exact edge.apply_right
    · exact edge
  have newStep (z : Option D) : p.SameCycle (project z) (project (q z)) := by
    cases z with
    | none =>
      change p.SameCycle a (project (subdivideBefore p a none))
      rw [subdivideBefore_none]
      exact SameCycle.rfl
    | some d =>
      change p.SameCycle d (project (subdivideBefore p a (some d)))
      rw [subdivideBefore_some]
      split <;> rename_i h
      · change p.SameCycle d a
        rw [← h]
        exact SameCycle.rfl.apply_right
      · exact SameCycle.rfl.apply_right
  have returns (z : Option D) : q.SameCycle (some (project z)) z := by
    cases z with
    | none =>
      change q.SameCycle (some a) none
      rw [← subdivideBefore_none p a]
      exact SameCycle.rfl.apply_left
    | some d => exact SameCycle.rfl
  exact Nat.card_congr (quotientEquivOfRetraction p q some project (fun _ => rfl)
    oldStep newStep returns)

end

/-- Suppressing a dart from a nonsingleton face preserves the face count. -/
theorem countCycles_removeNone [Finite D] (p : Perm (Option D)) (h : p none ≠ none) :
    countCycles (removeNone p) = countCycles p := by
  classical
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr h)
  have reconstruct : subdivideBefore (removeNone p) a = p := by
    rw [subdivideBefore, map_equiv_removeNone, ha, ← mul_assoc, swap_mul_self, one_mul]
  rw [← countCycles_subdivideBefore (removeNone p) a, reconstruct]

end MultiGenus.Surgery
