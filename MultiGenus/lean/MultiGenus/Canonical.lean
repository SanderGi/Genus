/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Faces
public import MultiGenus.Graph
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sections
import Mathlib.Data.List.GetD

/-! # Enumerating cyclic neighbor orders with a fixed first neighbor

For a vertex of positive degree, its first input neighbor anchors the cyclic order.
The choices at different vertices are independent.
-/

@[expose] public section

namespace MultiGenus.Canonical

open Rotations

/-- Keep the first input neighbor fixed and permute the remaining neighbors. -/
def orders : List Nat → List (List Nat)
  | [] => [[]]
  | a :: tail => tail.permutations.map (a :: ·)

/-- There are `(degree - 1)!` local orders, including one order for an isolated vertex. -/
theorem length_orders (ns : List Nat) : (orders ns).length = (ns.length - 1).factorial := by
  cases ns <;> simp [orders, List.length_permutations]

/-- Independent choices of one anchored neighbor order at each vertex. -/
def enumerate (n : Nat) (edges : List Edge) : List Rows :=
  ((List.range n).map fun v => orders (neighbors edges v)).sections

/-- Membership in the search is equivalent to the local anchored-order conditions. -/
theorem mem_enumerate {n : Nat} {edges : List Edge} {rows : Rows} :
    rows ∈ enumerate n edges ↔ rows.length = n ∧
      ∀ v < n, rows.getD v [] ∈ orders (neighbors edges v) := by
  rw [enumerate, List.mem_sections, List.forall₂_iff_get]
  simp only [List.length_map, List.length_range, List.get_eq_getElem, List.getElem_map,
    List.getElem_range]
  constructor
  · rintro ⟨len, h⟩
    refine ⟨len, fun v hv => ?_⟩
    simpa only [List.getD_eq_getElem rows [] (len ▸ hv)] using h v (len ▸ hv) hv
  · rintro ⟨len, h⟩
    exact ⟨len, fun v hr hv => by simpa only [List.getD_eq_getElem rows [] hr] using h v hv⟩

/-- The input neighbor order itself is one of the anchored orders. -/
theorem mem_orders_self (ns : List Nat) : ns ∈ orders ns := by
  cases ns with
  | nil => simp [orders]
  | cons a t => exact List.mem_map.mpr ⟨t, List.mem_permutations.mpr (.refl t), rfl⟩

/-- The input neighbor orders give a candidate even when the edge list is empty. -/
theorem input_mem_enumerate (n : Nat) (edges : List Edge) :
    ((List.range n).map (neighbors edges)) ∈ enumerate n edges := by
  apply mem_enumerate.mpr
  refine ⟨by simp, fun v hv => ?_⟩
  simpa [List.getD_eq_getElem?_getD, hv] using mem_orders_self (neighbors edges v)

/-- Canonical search always has at least one candidate. -/
theorem enumerate_ne_nil (n : Nat) (edges : List Edge) : enumerate n edges ≠ [] :=
  List.ne_nil_of_mem (input_mem_enumerate n edges)

private theorem perm_of_mem_orders {ns r : List Nat} (hr : r ∈ orders ns) : r.Perm ns := by
  cases ns with
  | nil => simpa [orders] using hr
  | cons a ns =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
    exact (List.mem_permutations.mp ht).cons a

/-- Every emitted rotation orders exactly the given incidences. -/
theorem legal_of_mem {n : Nat} {edges : List Edge} {rows : Rows}
    (h : rows ∈ enumerate n edges) : Legal n edges rows := by
  obtain ⟨len, localOrders⟩ := mem_enumerate.mp h
  exact ⟨len, fun v hv => perm_of_mem_orders (localOrders v hv)⟩

private theorem exists_order {r ns : List Nat} (h : r.Perm ns) :
    ∃ s ∈ orders ns, r.IsRotated s := by
  cases ns with
  | nil =>
    obtain rfl := List.perm_nil.mp h
    exact ⟨[], by simp [orders], .refl _⟩
  | cons a ns =>
    have ha := h.mem_iff.mpr (List.mem_cons_self (a := a) (l := ns))
    obtain ⟨pre, post, rfl, _⟩ := List.eq_append_cons_of_mem ha
    have rot := List.isRotated_append (l := pre) (l' := a :: post)
    have perm := (List.perm_cons a).mp (rot.perm.symm.trans h)
    exact ⟨_, List.mem_map.mpr ⟨_, List.mem_permutations.mpr perm, rfl⟩, rot⟩

private theorem isolated_iff (r : Rows) : r = [[]] ↔ r.length = 1 ∧ Faces.row r 0 = [] := by
  cases r with
  | nil => simp
  | cons a r => cases r <;> simp [Faces.row, List.getD_eq_getElem?_getD]

/-- Independently changing the starting points of the rows preserves the executable face count. -/
theorem faceCount_eq_of_rotated {r s : Rows} (len : r.length = s.length)
    (rot : ∀ v, (Faces.row r v).IsRotated (Faces.row s v))
    (nd : ∀ v, (Faces.row r v).Nodup) : Faces.faceCount r = Faces.faceCount s := by
  have ds : Faces.darts r = Faces.darts s := by
    ext ⟨u, v⟩
    simp only [Faces.mem_darts, len, (rot u).mem_iff]
  have step : Faces.faceStep r = Faces.faceStep s := by
    funext d
    exact congrArg (fun p : Equiv.Perm Nat => (d.2, p d.1))
      (List.formPerm_eq_of_isRotated (nd d.2) (rot d.2))
  have iso : r = [[]] ↔ s = [[]] := by
    rw [isolated_iff, isolated_iff, len]
    simp only [← List.length_eq_zero_iff, (rot 0).perm.length_eq]
  have walk : Faces.faceWalk r = Faces.faceWalk s := by
    funext d
    simp only [Faces.faceWalk, ds, step]
  simp only [Faces.faceCount, Faces.orbitCount, ds, walk, iso]

/-- Any legal rotation has an enumerated representative with the same number of faces. -/
theorem exists_same_faces {n : Nat} {edges : List Edge} {rows : Rows}
    (G : SimpleInput n edges) (h : Legal n edges rows) :
    ∃ r ∈ enumerate n edges, Faces.faceCount r = Faces.faceCount rows := by
  have nrows := h.1
  choose pick hm hr using fun i : Fin n => exists_order (h.2 i.val i.isLt)
  let r := List.ofFn pick
  have len : r.length = n := List.length_ofFn
  have get (v : Nat) (hv : v < n) : r.getD v [] = pick ⟨v, hv⟩ := by
    rw [List.getD_eq_getElem r [] (len ▸ hv)]
    simp [r]
  refine ⟨r, mem_enumerate.mpr ⟨len, fun v hv => get v hv ▸ hm ⟨v, hv⟩⟩, Eq.symm ?_⟩
  apply faceCount_eq_of_rotated (h.1.trans len.symm)
  · intro v
    by_cases hv : v < n
    · simpa only [Faces.row, get v hv] using hr ⟨v, hv⟩
    · simp [Faces.row, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
        rows.length ≤ v), List.getElem?_eq_none (by omega : r.length ≤ v)]
  · intro v
    by_cases hv : v < n
    · exact (h.2 v hv).nodup_iff.mpr (G.neighbors_nodup v)
    · simp [Faces.row, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
        rows.length ≤ v)]

end MultiGenus.Canonical
