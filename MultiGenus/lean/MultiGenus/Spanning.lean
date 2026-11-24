/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Graph
public import Mathlib.Data.Finset.Card

/-! # A tree-first edge order for connected graph search

Starting at vertex zero, choose the first remaining edge leaving the reached set.
Each choice reaches one new vertex and preserves the order of the remaining edges.
-/

@[expose] public section

namespace MultiGenus.Spanning

open Rotations Relation

/-- Test whether exactly one endpoint has been reached. -/
def crossing (seen : Finset Nat) (e : Edge) : Bool :=
  decide ((e.1 ∈ seen ∧ e.2 ∉ seen) ∨ (e.2 ∈ seen ∧ e.1 ∉ seen))

/-- The unreached endpoint of a crossing edge. -/
def outside (seen : Finset Nat) (e : Edge) : Nat :=
  if e.1 ∈ seen then e.2 else e.1

/-- Grow the rooted edge list by at most the given number of new vertices. -/
def grow : Nat → Finset Nat → List Edge → List Edge → List Edge × List Edge
  | 0, _, tree, rest => (tree, rest)
  | fuel + 1, seen, tree, rest =>
    match rest.find? (crossing seen) with
    | none => (tree, rest)
    | some e => grow fuel (insert (outside seen e) seen) (tree ++ [e]) (rest.erase e)

/-- Extract a spanning tree rooted at zero, breaking ties by input order. On a
disconnected graph growth stops when the component of zero has no outgoing edge. -/
def split (n : Nat) (edges : List Edge) : List Edge × List Edge :=
  grow (n - 1) {0} [] edges

private theorem extract_perm {e : Edge} {tree rest : List Edge} (h : e ∈ rest) :
    ((tree ++ [e]) ++ rest.erase e).Perm (tree ++ rest) := by
  simpa only [List.append_assoc, List.singleton_append] using
    (List.perm_cons_erase h).symm.append_left tree

private theorem grow_perm (fuel : Nat) (seen : Finset Nat) (tree rest : List Edge) :
    ((grow fuel seen tree rest).1 ++ (grow fuel seen tree rest).2).Perm (tree ++ rest) := by
  induction fuel generalizing seen tree rest with
  | zero => exact .refl _
  | succ fuel ih =>
    simp only [grow]
    split
    · exact .refl _
    · exact (ih ..).trans (extract_perm (List.mem_of_find?_eq_some ‹_›))

/-- The tree-first edge order contains every input edge with its original multiplicity. -/
theorem split_perm (n : Nat) (edges : List Edge) :
    ((split n edges).1 ++ (split n edges).2).Perm edges :=
  grow_perm (n - 1) {0} [] edges

private abbrev Path (es : List Edge) (a b : Nat) :=
  ReflTransGen (fun u v => v ∈ neighbors es u) a b

private theorem reverse_path {es : List Edge} {a b : Nat} (p : Path es a b) : Path es b a := by
  induction p with
  | refl => exact .refl
  | tail _ edge ih => exact .head (mem_neighbors.mpr (mem_neighbors.mp edge).symm) ih

private theorem extend_path {tree : List Edge} {e : Edge} {a b : Nat} (p : Path tree a b) :
    Path (tree ++ [e]) a b := by
  apply ReflTransGen.mono _ _ _ p
  intro u v h
  exact mem_neighbors.mpr
    ((mem_neighbors.mp h).imp (List.mem_append_left _) (List.mem_append_left _))

/-- While growing, the tree spans the reached set and each edge has added one vertex. -/
private structure State (n : Nat) (es : List Edge) (fuel : Nat) (seen : Finset Nat)
    (tree rest : List Edge) : Prop where
  perm : (tree ++ rest).Perm es
  root : 0 ∈ seen
  bounded : seen ⊆ Finset.range n
  spans : ∀ x ∈ seen, Path tree 0 x
  ends : ∀ e ∈ tree, e.1 ∈ seen ∧ e.2 ∈ seen
  size : tree.length + 1 = seen.card
  budget : fuel + seen.card = n

variable {n fuel : Nat} {es tree rest : List Edge} {seen : Finset Nat}

private theorem advance (G : SimpleInput n es) (s : State n es (fuel + 1) seen tree rest)
    {e : Edge} (choice : rest.find? (crossing seen) = some e) :
    State n es fuel (insert (outside seen e) seen) (tree ++ [e]) (rest.erase e) := by
  have hr := List.mem_of_find?_eq_some choice
  have he := s.perm.mem_iff.mp (List.mem_append_right tree hr)
  have cut : (e.1 ∈ seen ∧ e.2 ∉ seen) ∨ (e.2 ∈ seen ∧ e.1 ∉ seen) := by
    simpa only [crossing, decide_eq_true_eq] using List.find?_some choice
  have fresh : outside seen e ∉ seen := by
    rcases cut with h | h
    · simpa [outside, h.1] using h.2
    · simp [outside, h.2]
  have add : e ∈ tree ++ [e] := by simp
  have both : e.1 ∈ insert (outside seen e) seen ∧ e.2 ∈ insert (outside seen e) seen := by
    rcases cut with h | h <;> simp [outside, h.1, h.2]
  have reach : Path (tree ++ [e]) 0 (outside seen e) := by
    rcases cut with h | h
    · simp only [outside, h.1, ↓reduceIte]
      exact (extend_path (s.spans _ h.1)).tail (mem_neighbors.mpr (Or.inl add))
    · simp only [outside, h.2, ↓reduceIte]
      exact (extend_path (s.spans _ h.1)).tail (mem_neighbors.mpr (Or.inr add))
  have inRange : outside seen e < n := by
    unfold outside
    split
    · exact G.bounded _ he
    · exact lt_trans (G.ordered _ he) (G.bounded _ he)
  refine ⟨(extract_perm hr).trans s.perm, Finset.mem_insert_of_mem s.root, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr inRange
    · exact s.bounded hx
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact reach
    · exact extend_path (s.spans _ hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨Finset.mem_insert_of_mem (s.ends _ hx).1, Finset.mem_insert_of_mem (s.ends _ hx).2⟩
    · exact List.mem_singleton.mp hx ▸ both
  · simp [Finset.card_insert_of_notMem fresh, s.size]
  · rw [Finset.card_insert_of_notMem fresh]
    have := s.budget
    omega

private theorem all_reached (con : ConnectedInput n es) (s : State n es fuel seen tree rest)
    (none : rest.find? (crossing seen) = Option.none) : Finset.range n ⊆ seen := by
  have closed (u v : Nat) (hu : u ∈ seen) (edge : v ∈ neighbors es u) : v ∈ seen := by
    have ends {e : Edge} (he : e ∈ es) : e.1 ∈ seen ↔ e.2 ∈ seen := by
      rcases List.mem_append.mp (s.perm.mem_iff.mpr he) with ht | hr
      · exact ⟨fun _ => (s.ends _ ht).2, fun _ => (s.ends _ ht).1⟩
      · have h := List.find?_eq_none.mp none _ hr
        simp only [crossing, decide_eq_true_eq] at h
        tauto
    rcases mem_neighbors.mp edge with h | h
    · exact (ends h).mp hu
    · exact (ends h).mpr hu
  intro x hx
  have path := con.2 0 con.1 x (Finset.mem_range.mp hx)
  clear hx
  induction path with
  | refl => exact s.root
  | tail _ edge ih => exact closed _ _ ih edge

private theorem finish (hn : 0 < n) (s : State n es fuel seen tree rest)
    (full : Finset.range n ⊆ seen) : ConnectedInput n tree ∧ tree.length + 1 = n := by
  have eq := Finset.Subset.antisymm s.bounded full
  refine ⟨⟨hn, ?_⟩, by simpa [eq] using s.size⟩
  intro a ha b hb
  exact (reverse_path (s.spans a (full (Finset.mem_range.mpr ha)))).trans
    (s.spans b (full (Finset.mem_range.mpr hb)))

private theorem terminal (G : SimpleInput n es) (s : State n es fuel seen tree rest) :
    ∃ k reached, State n es k reached (grow fuel seen tree rest).1 (grow fuel seen tree rest).2 ∧
      (k = 0 ∨ (grow fuel seen tree rest).2.find? (crossing reached) = none) := by
  induction fuel generalizing seen tree rest with
  | zero => exact ⟨0, seen, s, Or.inl rfl⟩
  | succ fuel ih =>
    simp only [grow]
    split
    · exact ⟨fuel + 1, seen, s, Or.inr ‹_›⟩
    · exact ih (advance G s ‹_›)

private theorem split_terminal (G : SimpleInput n es) (hn : 0 < n) :
    ∃ k reached, State n es k reached (split n es).1 (split n es).2 ∧
      (k = 0 ∨ (split n es).2.find? (crossing reached) = none) := by
  apply terminal G
  refine ⟨.refl _, by simp, ?_, ?_, by simp, by simp, ?_⟩
  · simpa using hn
  · intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact .refl
  · simp; omega

private theorem split_spanning (G : SimpleInput n es) (con : ConnectedInput n es) :
    ConnectedInput n (split n es).1 ∧ (split n es).1.length + 1 = n := by
  obtain ⟨k, reached, s, stop⟩ := split_terminal G con.1
  apply finish con.1 s
  rcases stop with rfl | noCross
  · have eq := Finset.eq_of_subset_of_card_le s.bounded (by simpa using s.budget.ge)
    rw [eq]
  · exact all_reached con s noCross

/-- The selected edges connect all input vertices, including the single vertex
of a connected graph with no edges. -/
theorem connected_tree (G : SimpleInput n es) (con : ConnectedInput n es) :
    ConnectedInput n (split n es).1 := (split_spanning G con).1

/-- The connected output uses exactly one edge per vertex other than the root. -/
theorem tree_length (G : SimpleInput n es) (con : ConnectedInput n es) :
    (split n es).1.length + 1 = n := (split_spanning G con).2

/-- For a nonempty simple input, counting the selected edges decides connectivity. -/
theorem connected_iff_tree_length (G : SimpleInput n es) (hn : 0 < n) :
    ConnectedInput n es ↔ (split n es).1.length + 1 = n := by
  refine ⟨tree_length G, ?_⟩
  intro len
  obtain ⟨_, reached, s, _⟩ := split_terminal G hn
  have card : reached.card = n := s.size.symm.trans len
  have eq := Finset.eq_of_subset_of_card_le s.bounded (by simp [card])
  have treeCon := (finish hn s (by rw [eq])).1
  have inside {e : Edge} (he : e ∈ (split n es).1) : e ∈ es :=
    s.perm.mem_iff.mp (List.mem_append_left _ he)
  refine ⟨hn, fun a ha b hb => ReflTransGen.mono ?_ a b (treeCon.2 a ha b hb)⟩
  exact fun _ _ adj => mem_neighbors.mpr ((mem_neighbors.mp adj).imp inside inside)

end MultiGenus.Spanning
