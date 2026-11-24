/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySwap

/-! # Euler parity and the nonnegative genus of a connected rotation system

While all edge transpositions update the facial permutation, only those joining
different components update the auxiliary forest permutation. Its cycles contain
the facial cycles. A face merge within one component adds one to the genus.
-/

public section

namespace MultiGenus.Euler

open Equiv Equiv.Perm Surgery

variable {D : Type*}

private def Refines (p q : Perm D) : Prop :=
  ∀ x y, p.SameCycle x y → q.SameCycle x y

private def Connects (p : Perm D) (edges : List (D × D)) : Prop :=
  ∀ q : Perm D, Refines p q → (∀ e ∈ edges, q.SameCycle e.1 e.2) → ∀ x y, q.SameCycle x y

private theorem tail_connects {b c : Perm D} {e : D × D} {es : List (D × D)}
    (connected : Connects b (e :: es)) (hbc : Refines b c) (he : c.SameCycle e.1 e.2) :
    Connects c es := by
  intro q hcq htail
  apply connected q (fun x y h => hcq x y (hbc x y h))
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hcq _ _ he
  · exact htail d hd

variable [Finite D] [Nonempty D] [DecidableEq D]

/-- The count invariant for an arbitrary facial permutation refining the forest permutation. -/
private theorem forest_induction
    (edges : List (D × D)) (f c : Perm D) (ref : Refines f c)
    (distinct : ∀ e ∈ edges, e.1 ≠ e.2) (connected : Connects c edges) :
    ∃ g : Nat, 2 + edges.length + countCycles f =
      2 * countCycles c + countCycles (edges.foldl (fun p e => p * swap e.1 e.2) f) + 2 * g := by
  induction edges generalizing f c with
  | nil =>
    have hc := countCycles_eq_one_of_forall c (connected c (fun _ _ h => h) (by simp))
    exact ⟨0, by simp [hc]⟩
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    have hab : a ≠ b := distinct _ (.head _)
    have htail : ∀ e ∈ es, e.1 ≠ e.2 := fun e h => distinct e (.tail _ h)
    simp only [List.foldl_cons, List.length_cons]
    by_cases hc : c.SameCycle a b
    · obtain ⟨g, h⟩ := ih (f * swap a b) c
        (sameCycle_mul_swap_le f (SameCycle.setoid c) ref hc) htail
        (tail_connects connected (fun _ _ h => h) hc)
      by_cases hf : f.SameCycle a b
      · exact ⟨g, by have := countCycles_mul_swap_same f hab hf; omega⟩
      · exact ⟨g + 1, by have := countCycles_mul_swap_diff f hab hf; omega⟩
    · have le : Refines c (c * swap a b) :=
        fun _ _ => sameCycle_mul_swap_of_diff c hc
      have he := (sameCycle_mul_swap_endpoints c hab).mpr hc
      have ref' : Refines f (c * swap a b) := fun x y h => le x y (ref x y h)
      obtain ⟨g, h⟩ := ih (f * swap a b) (c * swap a b)
        (sameCycle_mul_swap_le f (SameCycle.setoid (c * swap a b)) ref' he)
        htail (tail_connects connected le he)
      have cf := countCycles_mul_swap_diff f hab (fun hf => hc (ref a b hf))
      have cc := countCycles_mul_swap_diff c hab hc
      exact ⟨g, by omega⟩

/-- Euler's formula for connected dart permutations gives an integral, nonnegative genus.
Connectivity says that any orbit partition containing the vertex cycles and identifying
the ends of every edge has a single class. -/
theorem exists_genus (p : Perm D) (edges : List (D × D))
    (distinct : ∀ e ∈ edges, e.1 ≠ e.2)
    (connected : ∀ q : Perm D, (∀ x y, p.SameCycle x y → q.SameCycle x y) →
      (∀ e ∈ edges, q.SameCycle e.1 e.2) → ∀ x y, q.SameCycle x y) :
    ∃ g : Nat, 2 + edges.length = countCycles p +
      countCycles (edges.foldl (fun f e => f * swap e.1 e.2) p) + 2 * g := by
  obtain ⟨g, h⟩ := forest_induction edges p p (fun _ _ h => h) distinct connected
  exact ⟨g, by omega⟩

end MultiGenus.Euler
