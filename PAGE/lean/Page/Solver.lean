/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.FaceBounds
public import Page.Layers
public import Page.Optimize
public import Page.Seed

/-! # Correctness of both minimum-genus PAGE searches -/

@[expose] public section

namespace Page

open MultiGenus MultiGenus.Rotations ExactCover FaceBounds

/-- The materialized strategy tries tables of increasing maximum face length.
The streaming strategy searches directly up to the largest possible facial length. -/
def searchLayers (stream : Bool) (n : Nat) (es : List Edge) (k : Nat) : Option Cover :=
  let cap := faceCap n es k
  if stream then Layers.search true n es cap k
  else (List.range (cap + 1)).findSome? fun limit => Layers.search false n es limit k

theorem searchLayers_sound {stream n es k fs} (h : searchLayers stream n es k = some fs) :
    Certificate.check n es fs = true ∧ fs.length = k := by
  cases stream with
  | true => exact Layers.search_sound h
  | false =>
    obtain ⟨_, _, found⟩ := List.exists_of_findSome?_eq_some h
    exact Layers.search_sound found

theorem searchLayers_iff {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (stream : Bool) (k : Nat) :
    (searchLayers stream n es k).isSome ↔ ∃ r, Legal n es r ∧ Faces.faceCount r = k := by
  rw [← Certificate.exists_check_iff_faces G]
  constructor
  · intro found
    obtain ⟨fs, h⟩ := Option.isSome_iff_exists.mp found
    exact ⟨fs, searchLayers_sound h⟩
  · rintro ⟨fs, hc, rfl⟩
    have atCap (s : Bool) := Layers.search_complete (stream := s) G con hc rfl
      (fun _ hf => length_le_cap G con hc hf)
    cases stream with
    | true => exact atCap true
    | false =>
      apply List.findSome?_isSome_iff.mpr
      exact ⟨_, List.mem_range.mpr (Nat.lt_succ_self _), atCap false⟩

/-- At the input rotation's face count, its traced face words already give a certificate. -/
def findFaces (stream : Bool) (n : Nat) (es : List Edge) (k : Nat) : Option Cover :=
  if k = Faces.faceCount (Seed.inputRows n es) then some (Seed.inputFaces n es)
  else searchLayers stream n es k

theorem findFaces_sound {stream n es k fs} (G : SimpleInput n es)
    (h : findFaces stream n es k = some fs) :
    Certificate.check n es fs = true ∧ fs.length = k := by
  unfold findFaces at h
  split at h
  · rename_i eq
    cases h
    exact ⟨Seed.check_inputFaces G, (Seed.length_inputFaces G).trans eq.symm⟩
  · exact searchLayers_sound h

theorem findFaces_iff {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (stream : Bool) (k : Nat) :
    (findFaces stream n es k).isSome ↔ ∃ r, Legal n es r ∧ Faces.faceCount r = k := by
  unfold findFaces
  split
  · rename_i eq
    simp only [Option.isSome_some, true_iff]
    exact ⟨_, (mem_enumerate_iff ..).mp (adjacency_mem_enumerate n es), eq.symm⟩
  · exact searchLayers_iff G con stream k

/-- Search the Euler targets from the certified face-length lower bound up to the
genus witnessed by the input ordering. -/
def solve (stream : Bool) (n : Nat) (es : List Edge) : Option (Nat × Cover) :=
  let lo := lowerGenus n es
  searchRange n es.length (findFaces stream n es) lo (upperGenus n es + 1 - lo)

/-- Minimum-genus search with precomputed tables of facial walks. -/
def materialized (n : Nat) (es : List Edge) := solve false n es

/-- Minimum-genus search generating rooted walks on demand. -/
def lowMemory (n : Nat) (es : List Edge) := solve true n es

/-- The returned faces reconstruct a legal rotation, satisfy Euler's formula,
and attain the least genus of any rotation of this input. -/
def Optimal (n : Nat) (es : List Edge) (g : Nat) (fs : Cover) : Prop :=
  Certificate.check n es fs = true ∧ Legal n es (Certificate.readRows n es fs) ∧
    Faces.faceCount (Certificate.readRows n es fs) = fs.length ∧
    2 + es.length = n + fs.length + 2 * g ∧ IsLeast {k | Realizes n es k} g

theorem solve_correct {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (stream : Bool) : ∃ g fs, solve stream n es = some (g, fs) ∧ Optimal n es g fs := by
  obtain ⟨fs, answer, exactF⟩ := searchRange_minimum G con _ (findFaces_iff G con stream)
    (lowerGenus_le_minimum G con)
  obtain ⟨hc, len⟩ := findFaces_sound G exactF
  have least := minimumGenus_isLeast G con
  obtain ⟨_, _, eq⟩ := least.1
  obtain ⟨legal, count⟩ := Certificate.readRows_of_check G hc
  refine ⟨_, fs, answer, hc, legal, count, ?_, least⟩
  unfold faceTarget at len
  omega

/-- Correctness of the materialized algorithm on every connected simple graph. -/
theorem materialized_correct {n es} (G : SimpleInput n es) (con : ConnectedInput n es) :
    ∃ g fs, materialized n es = some (g, fs) ∧ Optimal n es g fs :=
  solve_correct G con false

/-- Correctness of the low-memory algorithm on every connected simple graph. -/
theorem lowMemory_correct {n es} (G : SimpleInput n es) (con : ConnectedInput n es) :
    ∃ g fs, lowMemory n es = some (g, fs) ∧ Optimal n es g fs :=
  solve_correct G con true

/-- The two execution strategies always agree on the optimal genus. -/
theorem agree {n es} (G : SimpleInput n es) (con : ConnectedInput n es) :
    (materialized n es).map Prod.fst = (lowMemory n es).map Prod.fst := by
  obtain ⟨a, _, ha, _, _, _, _, la⟩ := materialized_correct G con
  obtain ⟨b, _, hb, _, _, _, _, lb⟩ := lowMemory_correct G con
  simp [ha, hb, la.unique lb]

end Page
