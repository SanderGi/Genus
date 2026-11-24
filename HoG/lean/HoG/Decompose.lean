/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.VertexSum
public import MultiGenus.Spanning
import Mathlib.Data.List.Nodup

/-! # Finding and certifying vertex-sum decompositions

Deleting a candidate cut vertex leaves a first component and its complement. Each child
retains the cut vertex as its local vertex zero. Before recursing we check connectivity,
simplicity, strict size decrease, and the neighbor rows under the inverse relabeling.
If no split passes these checks, the original graph becomes a direct-worker leaf.
-/

@[expose] public section

namespace HoG.Decompose

open MultiGenus MultiGenus.Rotations

/-- Grow a spanning tree from `start` after deleting all edges incident to `cut`. -/
def component (n : Nat) (es : List Edge) (cut start : Nat) : Finset Nat :=
  let rest := es.filter fun (u, v) => u != cut && v != cut
  let tree := (Spanning.grow n {start} [] rest).1
  insert start (tree.flatMap (fun (u, v) => [u, v])).toFinset

/-- Check whether the tree rooted at zero spans the input. -/
def connected? (n : Nat) (es : List Edge) : Bool :=
  decide (0 < n ∧ (Spanning.split n es).1.length + 1 = n)

theorem connected_of_check {n es} (G : SimpleInput n es) (h : connected? n es = true) :
    ConnectedInput n es := by
  obtain ⟨pos, spans⟩ := of_decide_eq_true h
  exact (Spanning.connected_iff_tree_length G pos).2 spans

/-- Check canonical endpoint ordering, bounds, and edge multiplicities. -/
scoped instance decidableSimpleInput {n es} : Decidable (SimpleInput n es) :=
  decidable_of_iff ((∀ e ∈ es, e.1 < e.2 ∧ e.2 < n) ∧ es.Nodup)
    ⟨fun h => ⟨fun e he => (h.1 e he).1, fun e he => (h.1 e he).2, h.2⟩,
     fun h => ⟨fun e he => ⟨h.ordered e he, h.bounded e he⟩, h.nodup⟩⟩

/-- A checked vertex sum with two strictly smaller connected simple summands. -/
structure Split (n : Nat) (es : List Edge) where
  /-- Left order, including the cut vertex. -/
  nL : Nat
  /-- Right order, including the cut vertex. -/
  nR : Nat
  /-- Left edges in local labels. -/
  esL : List Edge
  /-- Right edges in local labels. -/
  esR : List Edge
  simpleL : SimpleInput nL esL
  simpleR : SimpleInput nR esR
  connectedL : ConnectedInput nL esL
  connectedR : ConnectedInput nR esR
  nontrivialL : 1 < nL
  nontrivialR : 1 < nR
  smallerL : nL < n
  smallerR : nR < n
  /-- The canonical vertex sum has exactly the input graph's labeled adjacency
  after applying a single vertex bijection. -/
  relabel : ∃ e : Fin (VertexSum.vertices nL nR) ≃ Fin n,
    ∀ u v, v.val ∈ neighbors (VertexSum.edges nL esL esR) u.val ↔
      (e v).val ∈ neighbors es (e u).val

/-- Read a label from a vertex renumbering. -/
def label (names : List Nat) (i : Nat) : Nat := names[i]?.getD 0

private theorem label_get {names : List Nat} {i : Nat} (h : i < names.length) :
    label names i = names[i] := by simp [label, h]

/-- A permuted label list and matching neighbor rows induce a vertex bijection. -/
theorem relabel_of_rows {k n : Nat} {sumEdges es : List Edge} {names : List Nat}
    (G : SimpleInput k sumEdges) (len : names.length = k) (p : names.Perm (List.range n))
    (rows : ∀ i : Fin k, ((neighbors sumEdges i).map (label names)).Perm
      (neighbors es (label names i))) :
    ∃ e : Fin k ≃ Fin n, ∀ u v, v.val ∈ neighbors sumEdges u.val ↔
      (e v).val ∈ neighbors es (e u).val := by
  let f (i : Fin k) : Fin n := ⟨label names i, by
    rw [label_get (len ▸ i.isLt)]
    exact List.mem_range.mp (p.mem_iff.mp (List.getElem_mem _))⟩
  have inj : Function.Injective f := by
    intro a b eq
    have h : label names a = label names b := congrArg Fin.val eq
    rw [label_get (len ▸ a.isLt), label_get (len ▸ b.isLt)] at h
    exact Fin.ext ((p.nodup_iff.mpr List.nodup_range).getElem_inj_iff.mp h)
  have surj : Function.Surjective f := by
    intro b
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (p.mem_iff.mpr (List.mem_range.mpr b.isLt))
    exact ⟨⟨i, len ▸ hi⟩, Fin.ext ((label_get hi).trans e)⟩
  refine ⟨Equiv.ofBijective f ⟨inj, surj⟩, fun u v => ?_⟩
  change _ ↔ label names v ∈ neighbors es (label names u)
  rw [← (rows u).mem_iff]
  constructor
  · exact List.mem_map_of_mem
  · intro h
    obtain ⟨w, hw, eq⟩ := List.mem_map.mp h
    have same := inj (a₁ := ⟨w, G.neighbor_lt hw⟩) (a₂ := v) (Fin.ext eq)
    simpa only [← same] using hw

/-- Keep internal edges, renumber by position, and put the smaller endpoint first. -/
def induced (names : List Nat) (es : List Edge) : List Edge :=
  es.filterMap fun (u, v) =>
    let a := names.idxOf u
    let b := names.idxOf v
    if a < names.length ∧ b < names.length then some (min a b, max a b) else none

/-- Validate both children and their relabeling back to the input. -/
def certify (n : Nat) (es : List Edge) (cut : Nat) (left right : List Nat) :
    Option (Split n es) := do
  let nL := left.length + 1
  let nR := right.length + 1
  if sizes : 1 < nL ∧ nL < n ∧ 1 < nR ∧ nR < n then
    let esL := induced (cut :: left) es
    let esR := induced (cut :: right) es
    if good : SimpleInput nL esL ∧ SimpleInput nR esR ∧
        connected? nL esL = true ∧ connected? nR esR = true then
      let names := cut :: (left ++ right)
      let k := VertexSum.vertices nL nR
      let sumEdges := VertexSum.edges nL esL esR
      if cert : names.length = k ∧ names.Perm (List.range n) ∧
          ∀ i : Fin k, ((neighbors sumEdges i).map (label names)).Perm
            (neighbors es (label names i)) then
        return ⟨nL, nR, esL, esR, good.1, good.2.1, connected_of_check good.1 good.2.2.1,
          connected_of_check good.2.1 good.2.2.2, sizes.1, sizes.2.2.1, sizes.2.1, sizes.2.2.2,
          relabel_of_rows (VertexSum.simple good.1 good.2.1 (by omega)) cert.1 cert.2.1 cert.2.2⟩
  none

/-- Attempt a split at the given original vertex. Each child numbers that vertex zero. -/
def atVertex (n : Nat) (es : List Edge) (cut : Nat) : Option (Split n es) := do
  let others := (List.range n).erase cut
  let start ← others.head?
  let part := component n es cut start
  let (left, right) := others.partition (· ∈ part)
  certify n es cut left right

/-- Search for a cut vertex in input label order. -/
def findSplit (n : Nat) (es : List Edge) : Option (Split n es) :=
  (List.range n).findSome? (atVertex n es)

/-- A decomposition produced from an input, retaining structural evidence at every fork. -/
inductive Plan : Nat → List Edge → Type where
  | leaf (n : Nat) (es : List Edge) : Plan n es
  | split {n es} (s : Split n es) (left : Plan s.nL s.esL) (right : Plan s.nR s.esR) : Plan n es

/-- Recursively split at articulation vertices, including those incident to bridges. -/
def build (n : Nat) (es : List Edge) : Plan n es :=
  match findSplit n es with
  | none => .leaf n es
  | some s => .split s (build s.nL s.esL) (build s.nR s.esR)
termination_by n
decreasing_by all_goals first | exact s.smallerL | exact s.smallerR

/-- Invoke the worker on each leaf and add the two answers at each certified sum. -/
def Plan.fold {n : Nat} {es : List Edge} (p : Plan n es) (worker : Nat → List Edge → Option Nat) :
    Option Nat :=
  match p with
  | .leaf k cs => worker k cs
  | .split _ left right => do
    let l ← left.fold worker
    let r ← right.fold worker
    return l + r

/-- A correct direct worker lifts to any checked plan if the requested value adds
under each certified split. This induction also applies to the computed `build n es`. -/
theorem Plan.fold_eq_some {n es} (p : Plan n es) (value : Nat → List Edge → Nat)
    (worker : Nat → List Edge → Option Nat)
    (leaf : ∀ {k cs}, SimpleInput k cs → ConnectedInput k cs → worker k cs = some (value k cs))
    (add : ∀ {k cs} (s : Split k cs), SimpleInput k cs → ConnectedInput k cs →
      value k cs = value s.nL s.esL + value s.nR s.esR)
    (G : SimpleInput n es) (con : ConnectedInput n es) : p.fold worker = some (value n es) := by
  induction p with
  | leaf => exact leaf G con
  | split s _ _ ihL ihR =>
    simp [Plan.fold, ihL s.simpleL s.connectedL, ihR s.simpleR s.connectedR, add s G con]

end HoG.Decompose
