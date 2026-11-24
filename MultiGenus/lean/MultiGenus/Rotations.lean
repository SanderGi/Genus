/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Init.Data.List.Perm

/-! # Exhaustive rotation search by insertion at the endpoints of each edge -/

@[expose] public section

namespace MultiGenus.Rotations

/-- Each edge lists its two vertex indices, starting at zero. -/
abbrev Edge := Nat × Nat

/-- The row at each vertex lists its neighbors in cyclic order. Any starting point is allowed. -/
abbrev Rows := List (List Nat)

/-- Directed incidences at a vertex, read directly from the undirected input edge list. -/
def neighbors (edges : List Edge) (v : Nat) : List Nat :=
  edges.flatMap fun (a, b) => (if a = v then [b] else []) ++ (if b = v then [a] else [])

/-- A vertex has exactly one incidence row, in any order, for its neighbors. -/
def Legal (n : Nat) (edges : List Edge) (rows : Rows) : Prop :=
  rows.length = n ∧ ∀ v < n, (rows.getD v []).Perm (neighbors edges v)

/-- Insert a neighbor in every linear slot of a row, including both ends. -/
def slots (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: bs => (a :: b :: bs) :: (slots a bs).map (b :: ·)

/-- Choose an insertion slot in one vertex row. An absent vertex leaves the rows unchanged. -/
def insertNeighbor : Nat → Nat → Rows → List Rows
  | _, _, [] => [[]]
  | 0, a, r :: rs => (slots a r).map (· :: rs)
  | v + 1, a, r :: rs => (insertNeighbor v a rs).map (r :: ·)

/-- Choose a slot at each endpoint of an undirected edge. -/
def insertEdge (rows : Rows) (e : Edge) : List Rows :=
  (insertNeighbor e.1 e.2 rows).flatMap (insertNeighbor e.2 e.1)

/-- Extend seed rotations by inserting the remaining edges in their given order. -/
def extend (seeds : List Rows) (edges : List Edge) : List Rows :=
  edges.foldl (fun states e => states.flatMap (fun rows => insertEdge rows e)) seeds

/-- Enumerate local rotations starting from the empty row at every vertex. -/
def enumerate (n : Nat) (edges : List Edge) : List Rows :=
  extend [List.replicate n []] edges

/-- Enumeration can start with all tree rotations and extend them by the non-tree edges. -/
theorem enumerate_append (n : Nat) (tree rest : List Edge) :
    enumerate n (tree ++ rest) = extend (enumerate n tree) rest := by
  simp [enumerate, extend, List.foldl_append]

private theorem head_mem_slots (a : Nat) (xs : List Nat) : a :: xs ∈ slots a xs := by
  cases xs <;> simp [slots]

private theorem perm_of_mem_slots {a : Nat} {xs ys : List Nat} (h : ys ∈ slots a xs) :
    ys.Perm (a :: xs) := by
  induction xs generalizing ys with
  | nil => simpa [slots] using h
  | cons b bs ih =>
    simp only [slots, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨zs, hz, rfl⟩
    · exact .rfl
    · exact ((ih hz).cons b).trans (.swap _ _ _)

private theorem mem_slots_erase {a : Nat} {ys : List Nat} (h : a ∈ ys) :
    ys ∈ slots a (ys.erase a) := by
  induction ys with
  | nil => simp at h
  | cons b bs ih =>
    by_cases hb : b = a
    · subst b
      simpa using head_mem_slots a bs
    · have hm : a ∈ bs := (List.mem_cons.mp h).resolve_left (Ne.symm hb)
      simp [List.erase_cons_tail (a := a) (b := b), hb, slots, ih hm]

private theorem slot_spec (a : Nat) (xs ys : List Nat) :
    (∃ r, r.Perm xs ∧ ys ∈ slots a r) ↔ ys.Perm (a :: xs) := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact (perm_of_mem_slots h).trans (hr.cons a)
  · intro h
    obtain ⟨hm, he⟩ := List.cons_perm_iff_perm_erase.mp h.symm
    exact ⟨_, he.symm, mem_slots_erase hm⟩

private def rowwise : Nat → (Nat → List Nat) → Rows → Prop
  | 0, _, rs => rs = []
  | _ + 1, _, [] => False
  | n + 1, f, r :: rs => r.Perm (f 0) ∧ rowwise n (fun i => f (i+1)) rs

private theorem rowwise_iff (n : Nat) (f : Nat → List Nat) (rs : Rows) :
    rowwise n f rs ↔ rs.length = n ∧ ∀ i < n, (rs.getD i []).Perm (f i) := by
  induction n generalizing rs f with
  | zero =>
    simp [rowwise]
  | succ n ih =>
    cases rs with
    | nil => simp [rowwise]
    | cons r rs =>
      rw [rowwise, ih]
      constructor
      · rintro ⟨h, len, htail⟩
        refine ⟨by simp [len], ?_⟩
        intro i hi
        cases i with
        | zero => exact h
        | succ i => exact htail i (Nat.lt_of_succ_lt_succ hi)
      · rintro ⟨len, h⟩
        exact ⟨h 0 (Nat.zero_lt_succ _), by simpa using len,
          fun i hi => h (i+1) (Nat.succ_lt_succ hi)⟩

private def addAt (v a : Nat) (f : Nat → List Nat) (i : Nat) : List Nat :=
  if v = i then a :: f i else f i

private theorem addAt_succ (v a : Nat) (f : Nat → List Nat) :
    (fun i => addAt (v+1) a f (i+1)) = addAt v a (fun i => f (i+1)) := by
  funext i
  simp [addAt]

private theorem neighbor_spec (n v a : Nat) (f : Nat → List Nat) (ys : Rows) :
    (∃ rs, rowwise n f rs ∧ ys ∈ insertNeighbor v a rs) ↔ rowwise n (addAt v a f) ys := by
  induction n generalizing v f ys with
  | zero => simp [rowwise, insertNeighbor]
  | succ n ih =>
    constructor
    · rintro ⟨rs, hr, hy⟩
      cases rs with
      | nil => exact False.elim hr
      | cons r rs =>
        obtain ⟨hhead, htail⟩ := hr
        cases v with
        | zero =>
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
          exact ⟨(slot_spec a _ _).mp ⟨r, hhead, hz⟩, by simpa [addAt] using htail⟩
        | succ v =>
          obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp hy
          refine ⟨by simpa [addAt] using hhead, ?_⟩
          simpa only [addAt_succ] using (ih v (fun i => f (i+1)) zs).mp ⟨rs, htail, hz⟩
    · intro hy
      cases ys with
      | nil => exact False.elim hy
      | cons y ys =>
        obtain ⟨hy, htail⟩ := hy
        cases v with
        | zero =>
          obtain ⟨r, hr, hslot⟩ := (slot_spec a _ _).mpr hy
          exact ⟨r :: ys, ⟨hr, by simpa [addAt] using htail⟩, List.mem_map.mpr ⟨y, hslot, rfl⟩⟩
        | succ v =>
          obtain ⟨rs, hr, hins⟩ := (ih v (fun i => f (i+1)) ys).mpr (by
            simpa only [addAt_succ] using htail)
          exact ⟨y :: rs, ⟨by simpa [addAt] using hy, hr⟩, List.mem_map.mpr ⟨ys, hins, rfl⟩⟩

private theorem rowwise_congr {f g : Nat → List Nat} (h : ∀ i, (f i).Perm (g i))
    (n : Nat) (rs : Rows) : rowwise n f rs ↔ rowwise n g rs := by
  rw [rowwise_iff, rowwise_iff]
  exact and_congr_right fun _ => ⟨fun hs i hi => (hs i hi).trans (h i),
    fun hs i hi => (hs i hi).trans (h i).symm⟩

private theorem neighbors_insert (edges : List Edge) (e : Edge) (v : Nat) :
    (addAt e.2 e.1 (addAt e.1 e.2 (neighbors edges)) v).Perm (neighbors (edges ++ [e]) v) := by
  obtain ⟨a, b⟩ := e
  by_cases ha : a = v <;> by_cases hb : b = v
  all_goals simp [neighbors, addAt, List.flatMap_append, ha, hb]
  · subst a
    subst b
    exact List.perm_append_comm (l₁ := [v, v]) (l₂ := _)
  · exact (List.perm_append_singleton _ _).symm
  · exact (List.perm_append_singleton _ _).symm

/-- A legal rotation after one edge insertion comes from a legal rotation of the prefix. -/
theorem edge_spec (n : Nat) (edges : List Edge) (e : Edge) (ys : Rows) :
    (∃ rs, Legal n edges rs ∧ ys ∈ insertEdge rs e) ↔ Legal n (edges ++ [e]) ys := by
  change _ ↔ _ ∧ _
  rw [← rowwise_iff, ← rowwise_congr (neighbors_insert edges e),
    ← neighbor_spec,
    ← exists_congr (fun zs => and_congr_left (fun _ => neighbor_spec n e.1 e.2 _ zs))]
  constructor
  · rintro ⟨rs, h, hy⟩
    obtain ⟨zs, hz, hy⟩ := List.mem_flatMap.mp hy
    exact ⟨zs, ⟨rs, (rowwise_iff ..).mpr h, hz⟩, hy⟩
  · rintro ⟨zs, ⟨rs, hr, hz⟩, hy⟩
    exact ⟨rs, (rowwise_iff ..).mp hr, List.mem_flatMap.mpr ⟨zs, hz, hy⟩⟩

/-- Inserting an edge into a legal rotation preserves legality for the augmented edge list. -/
theorem legal_insertEdge {n : Nat} {pre : List Edge} {rs rs' : Rows} {e : Edge}
    (hr : Legal n pre rs) (h : rs' ∈ insertEdge rs e) : Legal n (pre ++ [e]) rs' :=
  (edge_spec ..).mp ⟨rs, hr, h⟩

/-- A complete search on a prefix remains complete after inserting any list of remaining edges. -/
theorem mem_extend_iff (n : Nat) (pre rest : List Edge) (seeds : List Rows)
    (hs : ∀ rs, rs ∈ seeds ↔ Legal n pre rs) (ys : Rows) :
    ys ∈ extend seeds rest ↔ Legal n (pre ++ rest) ys := by
  induction rest generalizing pre seeds with
  | nil => simpa [extend] using hs ys
  | cons e es ih =>
    have step (rs : Rows) :
        rs ∈ seeds.flatMap (fun r => insertEdge r e) ↔ Legal n (pre ++ [e]) rs := by
      simp only [List.mem_flatMap, hs, edge_spec]
    simpa [extend, List.append_assoc] using ih (pre ++ [e]) _ step

private theorem empty_spec (n : Nat) (rs : Rows) :
    rs = List.replicate n [] ↔ rowwise n (fun _ => []) rs := by
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    cases rs with
    | nil => simp [List.replicate_succ, rowwise]
    | cons r rs => simp [List.replicate_succ, rowwise, ih]

/-- An output occurs exactly when every vertex row permutes its independently computed
incidence list. In particular this covers every cyclic order of every loopless simple graph. -/
theorem mem_enumerate_iff (n : Nat) (edges : List Edge) (ys : Rows) :
    ys ∈ enumerate n edges ↔ Legal n edges ys := by
  apply mem_extend_iff n [] edges
  intro rs
  rw [List.mem_singleton, empty_spec]
  exact rowwise_iff ..

/-- Reading every incidence row in input order gives a candidate for the search. -/
theorem adjacency_mem_enumerate (n : Nat) (edges : List Edge) :
    (List.range n).map (neighbors edges) ∈ enumerate n edges := by
  apply (mem_enumerate_iff ..).mpr
  refine ⟨by simp, fun i hi => ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- Every graph has at least one candidate, including the graph with no incidences. -/
theorem enumerate_ne_nil (n : Nat) (edges : List Edge) : enumerate n edges ≠ [] :=
  List.ne_nil_of_mem (adjacency_mem_enumerate n edges)

end MultiGenus.Rotations
