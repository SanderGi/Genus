/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Mathlib.Data.List.Cycle
public import Mathlib.GroupTheory.Perm.List

/-! # Rooted dart-simple facial walk candidates

The materialized enumerator and the streaming depth-first traversal use the same
branch order. A branch removes each chosen directed edge from its available darts.
Revisiting a vertex is allowed, even after a prefix has already closed.
-/

@[expose] public section

namespace Page.Walks

/-- A directed edge represented by its two endpoints. -/
abbrev Dart := Nat × Nat

/-- A cyclic walk is stored without repeating its initial dart at the end. -/
abbrev Face := List Dart

/-- The head of one dart is the tail of its successor. -/
def Fits (a b : Dart) : Prop := a.2 = b.1

instance (a b : Dart) : Decidable (Fits a b) := inferInstanceAs (Decidable (a.2 = b.1))

/-- A nonempty closed walk using each of its darts once. -/
def Admissible (darts : List Dart) (f : Face) : Prop :=
  f ≠ [] ∧ f.Nodup ∧ f ⊆ darts ∧ Cycle.Chain Fits (f : Cycle Dart)

/-- A local successor test suffices to prove cyclic adjacency of a face. -/
theorem chain_of_next {f : Face} (hf : f.Nodup) (h : ∀ d ∈ f, Fits d (f.formPerm d)) :
    Cycle.Chain Fits (f : Cycle Dart) := by
  cases f with
  | nil => trivial
  | cons a l =>
    let f := a :: l
    change List.IsChain Fits (f ++ [a])
    apply List.isChain_append.mpr
    refine ⟨List.isChain_iff_getElem.mpr ?_, .singleton _, ?_⟩
    · intro i hi
      have hi₀ : i < f.length := by omega
      have e := h f[i] (List.getElem_mem hi₀)
      rwa [List.formPerm_apply_lt_getElem f hf i hi] at e
    · have ne : f ≠ [] := List.cons_ne_nil _ _
      have e := h (f.getLast ne) (List.getLast_mem ne)
      rw [List.formPerm_apply_getLast] at e
      simpa only [List.getLast?_eq_some_getLast ne, List.head?_cons, Option.mem_some_iff,
        forall_eq'] using e

/-- Optional empty continuation when the current dart closes the walk. -/
def close (root last : Dart) : List Face := if Fits last root then [[]] else []

/-- Remove the chosen dart from subsequent branches. -/
def without (free : List Dart) (d : Dart) : List Dart := free.filter (· != d)

/-- Materialize all completions of a prefix, taking at most `fuel` additional darts. -/
def tails (root last : Dart) (free : List Dart) : Nat → List Face
  | 0 => close root last
  | fuel + 1 => close root last ++ free.flatMap fun d =>
    if Fits last d then (tails root d (without free d) fuel).map (d :: ·) else []

/-- All dart-simple cyclic walks starting at the given dart. -/
def candidates (darts : List Dart) (root : Dart) : List Face :=
  let free := without darts root
  if root ∈ darts then (tails root root free free.length).map (root :: ·) else []

/-- Visit completions directly, stopping as soon as the continuation returns a witness. -/
def searchTails {α : Type*} (root last : Dart) (free : List Dart) (accept : Face → Option α) :
    Nat → Option α
  | 0 => if Fits last root then accept [] else none
  | fuel + 1 =>
    (if Fits last root then accept [] else none) <|> free.findSome? fun d =>
      if Fits last d then searchTails root d (without free d) (fun t => accept (d :: t)) fuel
      else none

/-- Search at a specified root without materializing a list of candidates. -/
def searchRoot {α : Type*} (darts : List Dart) (root : Dart) (accept : Face → Option α) :
    Option α :=
  let free := without darts root
  if root ∈ darts then searchTails root root free (fun t => accept (root :: t)) free.length
  else none

private theorem subset_without {t free : List Dart} {d : Dart} :
    t ⊆ without free d ↔ t ⊆ free ∧ d ∉ t := by
  unfold without
  grind

private theorem mem_close {t : Face} {root last : Dart} :
    t ∈ close root last ↔ t = [] ∧ Fits last root := by
  by_cases h : Fits last root <;> simp [close, h]

/-- Exact continuations of a prefix within the remaining length budget. -/
theorem mem_tails {root last : Dart} {free : List Dart} {t : Face} {fuel : Nat} :
    t ∈ tails root last free fuel ↔ t.length ≤ fuel ∧ t.Nodup ∧ t ⊆ free ∧
      List.IsChain Fits (last :: (t ++ [root])) := by
  induction fuel generalizing last free t with
  | zero => cases t <;> simp [tails, mem_close]
  | succ k ih =>
    cases t with
    | nil =>
      simp only [tails, List.mem_append, mem_close, List.mem_flatMap]
      simp +contextual [apply_ite (fun l : List Face => [] ∈ l)]
    | cons d t =>
      simp only [tails, List.mem_append, mem_close, List.cons_ne_nil, false_and, false_or,
        List.mem_flatMap, List.cons_append, List.isChain_cons_cons, List.length_cons,
        Nat.add_le_add_iff_right, List.nodup_cons, List.cons_subset]
      constructor
      · rintro ⟨e, he, h⟩
        split at h
        · rename_i fits
          obtain ⟨s, hs, eq⟩ := List.mem_map.mp h
          obtain ⟨rfl, rfl⟩ := List.cons.inj eq
          obtain ⟨len, nd, sub, chain⟩ := ih.mp hs
          obtain ⟨sub, fresh⟩ := subset_without.mp sub
          exact ⟨len, ⟨fresh, nd⟩, ⟨he, sub⟩, fits, chain⟩
        · contradiction
      · rintro ⟨len, ⟨fresh, nd⟩, ⟨hd, sub⟩, fits, chain⟩
        refine ⟨d, hd, ?_⟩
        rw [ite_eq_left fits]
        exact List.mem_map.mpr ⟨t, ih.mpr ⟨len, nd, subset_without.mpr ⟨sub, fresh⟩, chain⟩, rfl⟩

/-- Soundness and completeness at a fixed root, including walks with repeated vertices. -/
theorem mem_candidates_iff {darts : List Dart} {root : Dart} {f : Face} :
    f ∈ candidates darts root ↔ f.head? = some root ∧ Admissible darts f := by
  cases f with
  | nil => simp [candidates, apply_ite (fun l : List Face => [] ∈ l)]
  | cons a t =>
    by_cases hr : root ∈ darts
    · simp only [candidates, ite_eq_left hr, List.mem_map, List.cons.injEq, mem_tails,
        List.head?_cons, Option.some.injEq, Admissible, List.nodup_cons, List.cons_subset,
        Cycle.chain_coe_cons]
      constructor
      · rintro ⟨s, ⟨_, nd, sub, chain⟩, rfl, rfl⟩
        obtain ⟨su, fresh⟩ := subset_without.mp sub
        exact ⟨rfl, List.cons_ne_nil _ _, ⟨fresh, nd⟩, ⟨hr, su⟩, chain⟩
      · rintro ⟨rfl, _, ⟨fresh, nd⟩, ⟨_, su⟩, chain⟩
        have sub := subset_without.mpr ⟨su, fresh⟩
        exact ⟨t, ⟨nd.length_le_of_subset sub, nd, sub, chain⟩, rfl, rfl⟩
    · simp [candidates, hr, Admissible, List.cons_subset]
      grind

/-- Changing the starting point preserves dart-simple cyclic adjacency. -/
theorem admissible_isRotated {darts : List Dart} {f g : Face}
    (hf : Admissible darts f) (rot : f.IsRotated g) : Admissible darts g := by
  obtain ⟨ne, nd, sub, chain⟩ := hf
  refine ⟨fun eq => ne (List.isRotated_nil_iff.mp (eq ▸ rot)), rot.nodup_iff.mp nd,
    fun _ h => sub (rot.mem_iff.mpr h), ?_⟩
  rwa [← Cycle.coe_eq_coe.mpr rot]

/-- Every admissible face containing a dart appears, rotated to start at that dart. -/
theorem exists_rooted_of_mem {darts : List Dart} {f : Face} {d : Dart}
    (hf : Admissible darts f) (hd : d ∈ f) :
    ∃ g ∈ candidates darts d, f.IsRotated g := by
  obtain ⟨pre, post, rfl, _⟩ := List.eq_append_cons_of_mem hd
  have rot := List.isRotated_append (l := pre) (l' := d :: post)
  exact ⟨_, mem_candidates_iff.mpr ⟨rfl, admissible_isRotated hf rot⟩, rot⟩

private theorem findSome_flatMap {α β γ : Type*} (f : α → List β) (p : β → Option γ)
    (xs : List α) : (xs.flatMap f).findSome? p = xs.findSome? (fun x => (f x).findSome? p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.findSome?_cons, ih]
    cases (f x).findSome? p <;> rfl

/-- Streaming a bounded prefix visits the same continuations as its materialized list. -/
theorem searchTails_eq {α : Type*} (root last : Dart) (free : List Dart)
    (accept : Face → Option α) (fuel : Nat) :
    searchTails root last free accept fuel = (tails root last free fuel).findSome? accept := by
  induction fuel generalizing last free accept with
  | zero => by_cases h : Fits last root <;> simp [searchTails, tails, close, h]
  | succ k ih =>
    simp only [searchTails, tails, List.findSome?_append, findSome_flatMap]
    have children : (fun d => if Fits last d then
        searchTails root d (without free d) (fun t => accept (d :: t)) k else none) =
        (fun d => (if Fits last d then
          (tails root d (without free d) k).map (d :: ·) else []).findSome? accept) := by
      funext d
      by_cases h : Fits last d <;> simp [h, ih, List.findSome?_map, Function.comp_def]
    rw [children]
    by_cases h : Fits last root <;> simp [close, h]

/-- Both traversals return the same first successful continuation, including its result value. -/
theorem searchRoot_eq {α : Type*} (darts : List Dart) (root : Dart) (accept : Face → Option α) :
    searchRoot darts root accept = (candidates darts root).findSome? accept := by
  by_cases h : root ∈ darts <;> simp [searchRoot, candidates, h, searchTails_eq,
    List.findSome?_map, Function.comp_def]

end Page.Walks
