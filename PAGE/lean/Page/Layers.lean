/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.CheckedDFS

/-! # Face-length layers of the PAGE search

A length limit bounds the generator's recursion before it visits longer walks.
A table indexed by the first dart and an on-demand visitor solve the same
bounded exact-cover problem.
-/

@[expose] public section

namespace Page.Layers

open Walks ExactCover MultiGenus MultiGenus.Rotations

/-- Tables of rooted walks through the current maximum length. -/
def walks (u : List Dart) (d : Dart) (limit : Nat) : Cover :=
  if d ∈ u ∧ 0 < limit then
    (tails d d (without u d) (limit - 1)).map (d :: ·)
  else []

/-- Generate walks up to the limit, invoking the search as soon as a walk closes. -/
def visit (u : List Dart) (limit : Nat) : Finder := fun d next =>
  if d ∈ u ∧ 0 < limit then
    searchTails d d (without u d) (fun t => next (d :: t)) (limit - 1)
  else none

theorem visit_eq (u : List Dart) (limit : Nat) :
    visit u limit = fromLists (fun d => walks u d limit) := by
  funext d next
  by_cases h : d ∈ u ∧ 0 < limit <;>
    simp [visit, fromLists, walks, h, searchTails_eq, List.findSome?_map, Function.comp_def]

theorem mem_walks {u d limit f} : f ∈ walks u d limit ↔
    f ∈ candidates u d ∧ f.length ≤ limit := by
  by_cases hd : d ∈ u
  · cases f with
    | nil => simp [walks, candidates, hd, apply_ite (fun l : Cover => [] ∈ l)]
    | cons x t =>
      by_cases hl : 0 < limit
      · simp only [walks, hd, hl, and_self, ↓reduceIte, candidates, List.mem_map,
          List.cons.injEq, mem_tails, List.length_cons]
        constructor
        · rintro ⟨s, ⟨len, nd, sub, chain⟩, rfl, rfl⟩
          exact ⟨⟨_, ⟨nd.length_le_of_subset sub, nd, sub, chain⟩, rfl, rfl⟩, by omega⟩
        · rintro ⟨⟨s, ⟨_, nd, sub, chain⟩, rfl, rfl⟩, len⟩
          exact ⟨_, ⟨by omega, nd, sub, chain⟩, rfl, rfl⟩
      · simp [walks, show limit = 0 by omega]
  · simp [walks, candidates, hd]

/-- Validate a cover at one length limit. Rerooting preserves every length. -/
def within (n : Nat) (es : List Edge) (limit : Nat) (fs : Cover) : Bool :=
  Certificate.check n es fs && fs.all (fun f => f.length ≤ limit)

private theorem stable (n : Nat) (es : List Edge) (limit : Nat) :
    Invariant (within n es limit) := by
  constructor
  · intro xs ys p h
    simp only [within, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at *
    exact ⟨Certificate.check_perm p h.1, fun f hf => h.2 _ (p.mem_iff.mpr hf)⟩
  · intro f g fs p h
    simp only [within, Bool.and_eq_true, List.all_cons, decide_eq_true_eq] at *
    exact ⟨Certificate.check_rotate p h.1, p.perm.length_eq ▸ h.2.1, h.2.2⟩

/-- Search using one table for a maximum face length. -/
def materialized (u : List Dart) (lo limit k : Nat) (check pass : Cover → Bool) : Option Cover :=
  let table := u.map fun d => (d, walks u d limit)
  CheckedDFS.dfs (fun d next => ((table.lookup d).getD []).findSome? next)
    check pass lo limit k u []

/-- The streaming implementation retains no table of face words. -/
def streaming (u : List Dart) (lo limit k : Nat) (check pass : Cover → Bool) : Option Cover :=
  CheckedDFS.dfs (visit u limit) check pass lo limit k u []

theorem streaming_eq (u : List Dart) (lo limit k : Nat) (c pass : Cover → Bool) :
    streaming u lo limit k c pass = materialized u lo limit k c pass := by
  unfold streaming materialized
  rw [visit_eq]
  apply congrArg (fun find => CheckedDFS.dfs find c pass lo limit k u [])
  funext d next
  dsimp only [fromLists]
  rw [table_lookup]
  by_cases h : d ∈ u <;> simp [h, walks]

/-- The isolated vertex is represented by one face of length zero. -/
def search (stream : Bool) (n : Nat) (es : List Edge) (limit k : Nat) : Option Cover :=
  if n = 1 ∧ es = [] then
    if k = 1 then some [[]] else none
  else
    let u := Certificate.universe es
    let lo := FaceBounds.minLength n es
    let cap := min limit (FaceBounds.faceCap n es k)
    let c := within n es cap
    let pass := CheckedDFS.compatible fun v => (neighbors es v).length
    if k * lo ≤ u.length ∧ u.length ≤ k * cap then
      if stream then streaming u lo cap k c pass else materialized u lo cap k c pass
    else none

private theorem search_nonisolated {n es limit k stream} (hn : ¬(n = 1 ∧ es = [])) :
    let cap := min limit (FaceBounds.faceCap n es k)
    let u := Certificate.universe es
    let lo := FaceBounds.minLength n es
    search stream n es limit k = if k * lo ≤ u.length ∧ u.length ≤ k * cap then
      CheckedDFS.dfs (fromLists (fun d => walks u d cap)) (within n es cap)
        (CheckedDFS.compatible fun v => (neighbors es v).length) lo cap k u []
      else none := by
  cases stream <;> simp [search, hn, ← streaming_eq, streaming, visit_eq]

private theorem search_spec {stream n es limit k fs} (h : search stream n es limit k = some fs) :
    Certificate.check n es fs = true ∧ fs.length = k ∧ (∀ f ∈ fs, f.length ≤ limit) := by
  by_cases iso : n = 1 ∧ es = []
  · obtain ⟨rfl, rfl⟩ := iso
    by_cases h₁ : k = 1 <;> simp_all [search]
    grind
  · rw [search_nonisolated iso] at h
    split at h <;> try contradiction
    obtain ⟨ok, len⟩ := CheckedDFS.dfs_sound _ _ _ _ _ _ _ _ _ h
    simp only [within, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
    exact ⟨ok.1, by simpa using len, fun f hf => (ok.2 f hf).trans (min_le_left ..)⟩

theorem search_sound {stream n es limit k fs} (h : search stream n es limit k = some fs) :
    Certificate.check n es fs = true ∧ fs.length = k :=
  ⟨(search_spec h).1, (search_spec h).2.1⟩

/-- Any verified cover whose faces fit the current layer is reachable from that layer. -/
theorem search_complete {stream n es limit k fs} (G : SimpleInput n es)
    (con : ConnectedInput n es) (h : Certificate.check n es fs = true)
    (len : fs.length = k) (fits : ∀ f ∈ fs, f.length ≤ limit) :
    (search stream n es limit k).isSome := by
  by_cases iso : n = 1 ∧ es = []
  · obtain ⟨rfl, rfl⟩ := iso
    simp_all [search]
  · have ne : es ≠ [] := by
      rintro rfl
      have hn : 1 < n := by have := con.1; grind
      obtain ⟨w, hw⟩ := SimpleInput.exists_neighbor con hn 0 con.1
      simp [neighbors] at hw
    rw [search_nonisolated iso]
    have capped (f) (hf : f ∈ fs) : f.length ≤ min limit (FaceBounds.faceCap n es k) :=
      le_min (fits f hf) (len ▸ FaceBounds.length_le_cap G con h hf)
    have budget := CheckedDFS.flatten_bounds (fun f hf => ⟨FaceBounds.minLength_le G con h hf,
      capped f hf⟩)
    rw [len, (Certificate.check_flatten_perm h).length_eq] at budget
    rw [ite_eq_left budget]
    refine CheckedDFS.dfs_complete _ _ _ _ _ ?_ ?_ (stable ..) _ _ _ fs len
      (Certificate.check_flatten_perm h) ?_ ?_ ?_
    · intro rest pre ok
      exact CheckedDFS.compatible_of_check G (Bool.and_eq_true_iff.mp ok).1
        (List.sublist_append_right rest pre).subperm
    · intro cs ok f hf
      simp only [within, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
      exact ⟨FaceBounds.minLength_le G con ok.1 hf, ok.2 _ hf⟩
    · simpa [within, h, List.all_eq_true] using capped
    · exact fun f hf => (Certificate.check_face ne h hf).1
    · intro f hf d hd
      obtain ⟨g, hg, rot⟩ := exists_rooted_of_mem (Certificate.admissible_of_check ne h hf) hd
      exact ⟨g, mem_walks.mpr ⟨hg, rot.perm.length_eq ▸ capped f hf⟩, rot⟩

/-- At a fixed limit and face count, pruning preserves precisely the checked solutions'
existence for either generation strategy. -/
theorem search_isSome_iff {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (stream : Bool) (limit k : Nat) :
    (search stream n es limit k).isSome ↔
      ∃ fs, Certificate.check n es fs = true ∧ fs.length = k ∧ ∀ f ∈ fs, f.length ≤ limit := by
  constructor
  · intro found
    obtain ⟨fs, h⟩ := Option.isSome_iff_exists.mp found
    exact ⟨fs, search_spec h⟩
  · rintro ⟨fs, ok, len, fits⟩
    exact search_complete G con ok len fits

end Page.Layers
