/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.Certificate
import Mathlib.Data.List.Count

/-! # Exact face covers by depth-first search

At each node the first uncovered dart forces the next face to contain it. A
rooted walk generator passes one candidate to the continuation. The same search
can consume a precomputed table of walks or generate each walk on demand.
-/

@[expose] public section

namespace Page.ExactCover

/-- A cover contains cyclic face words on directed endpoint pairs. -/
abbrev Cover := List (List (Nat × Nat))

/-- A rooted generator may immediately return the certificate found by its continuation. -/
abbrev Finder := (Nat × Nat) → (List (Nat × Nat) → Option Cover) → Option Cover

/-- Search for exactly `left` more faces, keeping the uncovered darts in input order. -/
def dfs (find : Finder) (check : Cover → Bool) :
    (left : Nat) → List (Nat × Nat) → Cover → Option Cover
  | 0, [], chosen => if check chosen then some chosen else none
  | 0, _ :: _, _ => none
  | _ + 1, [], _ => none
  | k + 1, d :: ds, chosen =>
    find d fun f =>
      if f.all (· ∈ d :: ds) then dfs find check k ((d :: ds).diff f) (f :: chosen)
      else none

/-- Try a pivot’s candidate list in order, stopping at the first successful continuation. -/
def fromLists (pool : (Nat × Nat) → Cover) : Finder :=
  fun d next => (pool d).findSome? next

/-- A successful search extends the face count of the prefix and passes the leaf checker. -/
theorem dfs_sound (pool : (Nat × Nat) → Cover) (check : Cover → Bool) (k : Nat)
    (remaining : List (Nat × Nat)) (chosen result : Cover)
    (h : dfs (fromLists pool) check k remaining chosen = some result) :
    check result = true ∧ result.length = k + chosen.length := by
  induction k generalizing remaining chosen with
  | zero =>
    cases remaining with
    | nil =>
      simp only [dfs] at h
      split at h <;> simp_all
    | cons => simp [dfs] at h
  | succ k ih =>
    cases remaining with
    | nil => simp [dfs] at h
    | cons d ds =>
      obtain ⟨f, _, hf⟩ := List.exists_of_findSome?_eq_some h
      split at hf
      · obtain ⟨hc, hl⟩ := ih _ _ hf
        exact ⟨hc, by simp only [List.length_cons] at hl; omega⟩
      · contradiction

private theorem leftover {r f g : List (Nat × Nat)} {fs : Cover}
    (cov : r.Perm (f ++ fs.flatten)) (rot : f.IsRotated g) : fs.flatten.Perm (r.diff g) := by
  apply List.perm_iff_count.mpr
  intro d
  rw [List.count_diff, cov.count_eq, List.count_append, ← rot.perm.count_eq]
  omega

/-- The pivot rule may reorder faces and change the starting dart of a face. -/
structure Invariant (check : Cover → Bool) : Prop where
  /-- Permuting the faces preserves acceptance. -/
  perm : ∀ {xs ys : Cover}, xs.Perm ys → check xs = true → check ys = true
  /-- Rerooting the first face preserves acceptance. -/
  rotate : ∀ {f g : List (Nat × Nat)} {fs : Cover}, f.IsRotated g →
    check (f :: fs) = true → check (g :: fs) = true

/-- An accepted completion is found if every pending face can be rerooted at any of its darts. -/
theorem dfs_complete (pool : (Nat × Nat) → Cover) (check : Cover → Bool)
    (stable : Invariant check) (k : Nat) (remaining : List (Nat × Nat)) (chosen pending : Cover)
    (len : pending.length = k) (cov : pending.flatten.Perm remaining)
    (ok : check (pending ++ chosen) = true)
    (nonempty : ∀ f ∈ pending, f ≠ [])
    (rooted : ∀ f ∈ pending, ∀ d ∈ f, ∃ g ∈ pool d, f.IsRotated g) :
    (dfs (fromLists pool) check k remaining chosen).isSome := by
  induction k generalizing remaining chosen pending with
  | zero =>
    have hp : pending = [] := List.length_eq_zero_iff.mp len
    subst pending
    have hr : remaining = [] := cov.symm.eq_nil
    subst remaining
    simpa [dfs] using ok
  | succ k ih =>
    cases remaining with
    | nil =>
      obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < pending.length)
      have emp := cov.eq_nil
      simp only [List.flatten_cons, List.append_eq_nil_iff] at emp
      exact (nonempty _ (.head _) emp.1).elim
    | cons d ds =>
      obtain ⟨f, hf, hd⟩ := List.mem_flatten.mp (cov.mem_iff.mpr (.head _))
      obtain ⟨g, hg, rot⟩ := rooted f hf d hd
      let rest := pending.erase f
      have pick : pending.Perm (f :: rest) := List.perm_cons_erase hf
      have parts : (d :: ds).Perm (f ++ rest.flatten) := cov.symm.trans pick.flatten
      have fits : ∀ x ∈ g, x ∈ d :: ds := fun x hx =>
        parts.mem_iff.mpr (List.mem_append_left _ (rot.perm.mem_iff.mpr hx))
      change ((pool d).findSome? _).isSome
      apply List.findSome?_isSome_iff.mpr
      refine ⟨g, hg, ?_⟩
      have allowed : g.all (fun x => decide (x ∈ d :: ds)) = true :=
        List.all_eq_true.mpr fun x hx => decide_eq_true (fits x hx)
      simp only [allowed, ite_true]
      apply ih _ _ rest (by simp [rest, hf, len]) (leftover parts rot)
      · have h₁ := stable.perm (pick.append_right chosen) ok
        have h₂ := stable.rotate rot (show check (f :: (rest ++ chosen)) = true from h₁)
        exact stable.perm List.perm_middle.symm h₂
      · exact fun f hf => nonempty f (List.mem_of_mem_erase hf)
      · exact fun f hf => rooted f (List.mem_of_mem_erase hf)

/-- Materialize the rooted candidate lists once and reuse them at every search node. -/
def materialized (darts : List Walks.Dart) (target : Nat) (check : Cover → Bool) : Option Cover :=
  let table := darts.map fun d => (d, Walks.candidates darts d)
  dfs (fun d next => ((table.lookup d).getD []).findSome? next) check target darts []

/-- Interleave rooted walk generation with exact-cover backtracking. -/
def streaming (darts : List Walks.Dart) (target : Nat) (check : Cover → Bool) : Option Cover :=
  dfs (Walks.searchRoot darts) check target darts []

/-- A materialized table returns the generator’s list at every stored root. -/
theorem table_lookup (pool : Walks.Dart → Cover) (ds : List Walks.Dart) (d : Walks.Dart) :
    ((ds.map fun x => (x, pool x)).lookup d).getD [] = if d ∈ ds then pool d else [] := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    by_cases h : d = x
    · subst x; simp
    · have eq : (d == x) = false := beq_eq_false_iff_ne.mpr h
      simpa [List.lookup_cons, eq, h] using ih

private theorem materialized_eq (u : List Walks.Dart) (k : Nat) (c : Cover → Bool) :
    materialized u k c = dfs (fromLists (Walks.candidates u)) c k u [] := by
  apply congrArg (fun find => dfs find c k u [])
  funext d next
  dsimp only [fromLists]
  rw [table_lookup]
  by_cases h : d ∈ u <;> simp [h, Walks.candidates]

/-- Both traversals return the same first certificate. -/
theorem streaming_eq_materialized (u : List Walks.Dart) (k : Nat) (c : Cover → Bool) :
    streaming u k c = materialized u k c := by
  rw [materialized_eq]
  unfold streaming
  congr 1
  funext d next
  exact Walks.searchRoot_eq ..

/-- Each returned certificate passes the final checker and contains exactly the requested faces. -/
theorem materialized_sound {u : List Walks.Dart} {k : Nat} {c : Cover → Bool} {fs : Cover}
    (h : materialized u k c = some fs) : c fs = true ∧ fs.length = k := by
  rw [materialized_eq] at h
  simpa using dfs_sound _ _ _ _ _ _ h

/-- Every accepted exact cover by admissible face words is found, up to face order and rooting. -/
theorem materialized_isSome_iff (u : List Walks.Dart) (k : Nat) (c : Cover → Bool)
    (stable : Invariant c)
    (cover : ∀ fs, c fs = true → fs.flatten.Perm u)
    (faces : ∀ fs, c fs = true → ∀ f ∈ fs, Walks.Admissible u f) :
    (materialized u k c).isSome ↔ ∃ fs, c fs = true ∧ fs.length = k := by
  constructor
  · intro h
    obtain ⟨fs, hfs⟩ := Option.isSome_iff_exists.mp h
    exact ⟨fs, materialized_sound hfs⟩
  · rintro ⟨fs, hf, hl⟩
    rw [materialized_eq]
    exact dfs_complete _ c stable k u [] fs hl (cover fs hf) (by simpa using hf)
      (fun f hm => (faces fs hf f hm).1)
      (fun f hm _ hd => Walks.exists_rooted_of_mem (faces fs hf f hm) hd)

open MultiGenus MultiGenus.Rotations

/-- Use the certificate convention of one empty face for the isolated vertex. -/
def searchWith (solver : List Walks.Dart → Nat → (Cover → Bool) → Option Cover)
    (n : Nat) (edges : List Edge) (target : Nat) : Option Cover :=
  if n = 1 ∧ edges = [] then
    if target = 1 then some [[]] else none
  else solver (Certificate.universe edges) target (Certificate.check n edges)

/-- Exact face-cover search using precomputed candidates. -/
def materializedSearch (n : Nat) (edges : List Edge) (target : Nat) : Option Cover :=
  searchWith materialized n edges target

/-- Exact face-cover search using on-demand rooted walk DFS. -/
def streamingSearch (n : Nat) (edges : List Edge) (target : Nat) : Option Cover :=
  searchWith streaming n edges target

/-- The low-memory and precomputed searches return identical optional certificates. -/
theorem streamingSearch_eq_materializedSearch (n : Nat) (edges : List Edge) (target : Nat) :
    streamingSearch n edges target = materializedSearch n edges target := by
  simp only [streamingSearch, materializedSearch, searchWith, streaming_eq_materialized]

/-- A successful materialized search provides the claimed number of verified faces. -/
theorem materializedSearch_sound {n target : Nat} {edges : List Edge} {fs : Cover}
    (h : materializedSearch n edges target = some fs) :
    Certificate.check n edges fs = true ∧ fs.length = target := by
  unfold materializedSearch searchWith at h
  split at h
  · rename_i iso
    obtain ⟨rfl, rfl⟩ := iso
    split at h
    · cases h
      simp_all
    · contradiction
  · exact materialized_sound h

/-- A successful streaming search provides the claimed number of verified faces. -/
theorem streamingSearch_sound {n target : Nat} {edges : List Edge} {fs : Cover}
    (h : streamingSearch n edges target = some fs) :
    Certificate.check n edges fs = true ∧ fs.length = target :=
  materializedSearch_sound ((streamingSearch_eq_materializedSearch ..).symm.trans h)

/-- Completeness for connected simple inputs, including the isolated vertex. -/
theorem materializedSearch_isSome_iff {n : Nat} {edges : List Edge} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (target : Nat) :
    (materializedSearch n edges target).isSome ↔
      ∃ fs, Certificate.check n edges fs = true ∧ fs.length = target := by
  by_cases hn : n = 1
  · subst n
    have empty : edges = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have := G.ordered e he
      have := G.bounded e he
      omega
    subst edges
    by_cases k : target = 1
    · simp [materializedSearch, searchWith, k]
    · simp [materializedSearch, searchWith, k, Ne.symm k]
  · have he : edges ≠ [] := by
      rintro rfl
      have pos := con.1
      obtain ⟨w, hw⟩ := SimpleInput.exists_neighbor con (by omega : 1 < n) 0 pos
      simp [neighbors] at hw
    simp only [materializedSearch, searchWith, hn, false_and, ite_false]
    exact materialized_isSome_iff _ _ _ ⟨Certificate.check_perm, Certificate.check_rotate⟩
      (fun _ => Certificate.check_flatten_perm)
      (fun _ h _ hf => Certificate.admissible_of_check he h hf)

/-- On-demand DFS succeeds exactly for the face counts admitted by the verifier. -/
theorem streamingSearch_isSome_iff {n : Nat} {edges : List Edge} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (target : Nat) :
    (streamingSearch n edges target).isSome ↔
      ∃ fs, Certificate.check n edges fs = true ∧ fs.length = target := by
  rw [streamingSearch_eq_materializedSearch, materializedSearch_isSome_iff G con]

end Page.ExactCover
