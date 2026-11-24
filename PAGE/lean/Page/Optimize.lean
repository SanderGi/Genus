/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Search

/-! # Euler targets and the search for the first attainable genus -/

@[expose] public section

namespace Page

open MultiGenus MultiGenus.Rotations

/-- Number of faces needed for a genus-`g` solution on `n` vertices and `m` edges. -/
def faceTarget (n m g : Nat) := m + 2 - (n + 2 * g)

/-- Each genus increment removes two faces from a feasible Euler target. -/
theorem faceTarget_succ {n m g : Nat} :
    faceTarget n m (g + 1) = faceTarget n m g - 2 := by
  unfold faceTarget
  omega

/-- Try an exact face-cover search at successively larger genera. -/
def searchRange {α : Type*} (n m : Nat) (findCover : Nat → Option α) (g : Nat) :
    Nat → Option (Nat × α)
  | 0 => none
  | fuel + 1 =>
    match findCover (faceTarget n m g) with
    | some fs => some (g, fs)
    | none => searchRange n m findCover (g + 1) fuel

private theorem first_success {α : Type*} (n m : Nat) (findCover : Nat → Option α)
    (least : Nat) (below : ∀ g < least, findCover (faceTarget n m g) = none)
    (found : (findCover (faceTarget n m least)).isSome) (lo fuel : Nat)
    (hlo : lo ≤ least) (hi : least < lo + fuel) :
    ∃ fs, searchRange n m findCover lo fuel = some (least, fs) ∧
      findCover (faceTarget n m least) = some fs := by
  induction fuel generalizing lo with
  | zero => omega
  | succ fuel ih =>
    by_cases same : lo = least
    · subst lo
      obtain ⟨fs, eq⟩ := Option.isSome_iff_exists.mp found
      exact ⟨fs, by simp [searchRange, eq], eq⟩
    · have lt : lo < least := by omega
      simpa [searchRange, below lo lt] using ih (lo + 1) (by omega) (by omega)

/-- The input's given order of neighbors is a rotation furnishing a finite upper bound. -/
def upperGenus (n : Nat) (edges : List Edge) : Nat :=
  genusOf n edges.length ((List.range n).map (neighbors edges))

theorem minimum_le_upper {n edges} (G : SimpleInput n edges) (con : ConnectedInput n edges) :
    minimumGenus n edges ≤ upperGenus n edges := by
  have h := (mem_enumerate_iff ..).mp (adjacency_mem_enumerate n edges)
  exact (minimumGenus_isLeast G con).2 ⟨_, h, euler_genus G con h⟩

/-- With a sound initial lower bound, an exact search returns a certificate of the minimum. -/
theorem searchRange_minimum {α : Type*} {n edges} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (findCover : Nat → Option α)
    (exactCount : ∀ f, (findCover f).isSome ↔ ∃ r, Legal n edges r ∧ Faces.faceCount r = f)
    {lo : Nat} (hlo : lo ≤ minimumGenus n edges) :
    ∃ fs, searchRange n edges.length findCover lo (upperGenus n edges + 1 - lo) =
      some (minimumGenus n edges, fs) ∧
      findCover (faceTarget n edges.length (minimumGenus n edges)) = some fs := by
  have least := minimumGenus_isLeast G con
  obtain ⟨best, hbest, euler⟩ := least.1
  have nonneg : n + 2 * minimumGenus n edges ≤ edges.length + 2 := by omega
  apply first_success
  · intro g lt
    apply Option.not_isSome_iff_eq_none.mp
    intro h
    obtain ⟨r, hr, faces⟩ := (exactCount _).mp h
    have realizes : Realizes n edges g := by
      refine ⟨r, hr, ?_⟩
      unfold faceTarget at faces
      omega
    exact (least.2 realizes).not_gt lt
  · apply (exactCount _).mpr
    exact ⟨best, hbest, by unfold faceTarget; omega⟩
  · exact hlo
  · have := minimum_le_upper G con
    omega

end Page
