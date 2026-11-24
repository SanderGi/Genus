/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySwap

/-! # Maximizing the number of faces meeting a cut vertex

Fix the exterior first-return permutation `p`. Splitting a cycle of `p` needs one
transposition and changes the face count by one. Conversely, starting at its inverse
and joining cycles constructs a cyclic vertex rotation attaining the resulting bound.
-/

public section

namespace HoG.Boundary

open Equiv Equiv.Perm MultiGenus.Surgery

variable {B : Type*} [Finite B]

omit [Finite B] in
private theorem count_one : countCycles (1 : Perm B) = Nat.card B := by
  let f : B → Quotient (SameCycle.setoid (1 : Perm B)) := Quotient.mk _
  apply (Nat.card_congr (Equiv.ofBijective f ⟨?_, Quotient.mk_surjective⟩)).symm
  intro x y h
  exact sameCycle_one.mp (Quotient.exact h)

private theorem count_le_card (p : Perm B) : countCycles p ≤ Nat.card B :=
  Nat.card_le_card_of_surjective (Quotient.mk (SameCycle.setoid p)) Quotient.mk_surjective

private theorem upper_aux (p r : Perm B) :
    countCycles (r * p) + countCycles p ≤ Nat.card B + countCycles r := by
  classical
  by_cases id : p = 1
  · simp [id, count_one, Nat.add_comm]
  obtain ⟨a, ha⟩ : ∃ a, a ≠ p a := by
    by_contra! h
    exact id (Equiv.ext fun a => (h a).symm)
  let s := swap a (p a)
  have cc := countCycles_mul_swap_same p ha (sameCycle_apply_right.mpr SameCycle.rfl)
  have smaller : Nat.card B - countCycles (p * s) < Nat.card B - countCycles p := by
    have := count_le_card (p * s)
    change countCycles (p * s) = _ at cc
    omega
  have ih := upper_aux (p * s) r
  rw [← mul_assoc] at ih
  by_cases h : (r * p).SameCycle a (p a)
  · have := countCycles_mul_swap_same (r * p) ha h
    dsimp [s] at ih
    omega
  · have := countCycles_mul_swap_diff (r * p) ha h
    dsimp [s] at ih
    omega
termination_by Nat.card B - countCycles p

variable [Nonempty B]

/-- A single cyclic ordering at the cut vertex bounds the number of incident faces. -/
theorem upper (p r : Perm B) (cyc : ∀ x y, r.SameCycle x y) :
    countCycles (r * p) + countCycles p ≤ Nat.card B + 1 := by
  simpa only [countCycles_eq_one_of_forall r cyc] using upper_aux p r

private theorem join_cycles (p r : Perm B) :
    ∃ t : Perm B, (∀ x y, t.SameCycle x y) ∧
      countCycles (r * p) + 1 ≤ countCycles (t * p) + countCycles r := by
  classical
  by_cases all : ∀ x y, r.SameCycle x y
  · exact ⟨r, all, by rw [countCycles_eq_one_of_forall r all]⟩
  push Not at all
  obtain ⟨a, b, hab⟩ := all
  have ne : a ≠ b := fun eq => hab (eq ▸ SameCycle.rfl)
  have cc := countCycles_swap_mul_diff r ne hab
  have smaller : countCycles (swap a b * r) < countCycles r := by omega
  obtain ⟨t, ht, ih⟩ := join_cycles p (swap a b * r)
  rw [mul_assoc] at ih
  refine ⟨t, ht, ?_⟩
  by_cases h : (r * p).SameCycle a b
  · have := countCycles_swap_mul_same (r * p) ne h
    omega
  · have := countCycles_swap_mul_diff (r * p) ne h
    omega
termination_by countCycles r

/-- Some cyclic ordering attains the upper bound for the fixed exterior excursions. -/
theorem attains (p : Perm B) :
    ∃ r : Perm B, (∀ x y, r.SameCycle x y) ∧
      countCycles (r * p) + countCycles p = Nat.card B + 1 := by
  obtain ⟨r, hr, h⟩ := join_cycles p p⁻¹
  simp only [inv_mul_cancel, count_one, countCycles_inv] at h
  exact ⟨r, hr, le_antisymm (upper p r hr) h⟩

end HoG.Boundary
