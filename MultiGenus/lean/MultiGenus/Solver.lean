/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Backtrack
public import MultiGenus.LowerBound
public import MultiGenus.Search
public import MultiGenus.Spanning

/-! # Correctness of the tree-first MultiGenus algorithm -/

@[expose] public section

namespace MultiGenus

open Rotations

/-- Search from all spanning-tree rotations for one witness of the requested genus. -/
def exactGenus (n : Nat) (edges : List Edge) (target : Nat) : Option Rows :=
  let (tree, rest) := Spanning.split n edges
  Backtrack.exactFrom n target tree rest

/-- Exact-genus search succeeds if and only if a rotation of that genus exists. -/
theorem exactGenus_iff {n t : Nat} {edges : List Edge} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) : (exactGenus n edges t).isSome ↔ Realizes n edges t := by
  have p := Spanning.split_perm n edges
  rw [exactGenus, Backtrack.exactFrom_iff (G.perm p.symm) (Spanning.connected_tree G con)]
  simp only [Realizes, legal_perm p, p.length_eq]

/-- The witness returned by `exactGenus` orders the original incidences and has genus `t`. -/
theorem exactGenus_sound {n t : Nat} {edges : List Edge} {r : Rows}
    (found : exactGenus n edges t = some r) : Legal n edges r ∧ genusOf n edges.length r = t := by
  have p := Spanning.split_perm n edges
  obtain ⟨hr, hg⟩ := Backtrack.exactFrom_sound found
  exact ⟨(legal_perm p).mp hr, p.length_eq ▸ hg⟩

/-- Try successively larger target genera, stopping at the first witness. -/
def deepen (search : Nat → Option Rows) (start : Nat) : Nat → Option (Nat × Rows)
  | 0 => none
  | fuel + 1 => match search start with
    | some r => some (start, r)
    | none => deepen search (start + 1) fuel

private theorem deepen_first (search : Nat → Option Rows) (g : Nat)
    (noneBelow : ∀ j < g, search j = none) (success : (search g).isSome)
    (fuel start : Nat) (lo : start ≤ g) (hi : g < start + fuel) :
    ∃ r, deepen search start fuel = some (g, r) ∧ search g = some r := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases eq : start = g
    · subst start
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp success
      exact ⟨r, by simp [deepen, hr], hr⟩
    · have lt : start < g := by omega
      simpa [deepen, noneBelow start lt] using ih (start + 1) (by omega) (by omega)

/-- Compute minimum genus and a witnessing rotation. The search starts at the certified
face-length bound. Any input ordering of the incidences supplies a finite upper bound. -/
def solve (n : Nat) (edges : List Edge) : Option (Nat × Rows) :=
  let lo := LowerBound.initial n edges
  let hi := genusOf n edges.length ((List.range n).map (neighbors edges))
  deepen (exactGenus n edges) lo (hi + 1 - lo)

/-- On every connected nonempty simple graph the executable search terminates with a witness.
Its Euler genus is the least genus realized by any cyclic ordering of the input graph. -/
theorem solve_correct {n : Nat} {edges : List Edge} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) :
    ∃ g r, solve n edges = some (g, r) ∧ Legal n edges r ∧
      2 + edges.length = n + Faces.faceCount r + 2 * g ∧ IsLeast {k | Realizes n edges k} g := by
  let g := minimumGenus n edges
  have least := minimumGenus_isLeast G con
  have below (j : Nat) (lt : j < g) : exactGenus n edges j = none := by
    by_contra notNone
    have realized := (exactGenus_iff G con).mp (Option.isSome_iff_ne_none.mpr notNone)
    exact (Nat.not_le_of_lt lt) (least.2 realized)
  have lo : LowerBound.initial n edges ≤ g := LowerBound.initial_le G con (bestRotation_legal ..)
  have hr := (mem_enumerate_iff ..).mp (adjacency_mem_enumerate n edges)
  have upper : g ≤ genusOf n edges.length ((List.range n).map (neighbors edges)) :=
    least.2 ⟨_, hr, euler_genus G con hr⟩
  obtain ⟨r, found, exactR⟩ := deepen_first (exactGenus n edges) g below
    ((exactGenus_iff G con).mpr least.1)
    (genusOf n edges.length ((List.range n).map (neighbors edges)) + 1 - LowerBound.initial n edges)
    (LowerBound.initial n edges) lo (by omega)
  obtain ⟨legal, genus⟩ := exactGenus_sound exactR
  exact ⟨g, r, found, legal, genus ▸ euler_genus G con legal, least⟩

end MultiGenus
