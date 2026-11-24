/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Extension
public import MultiGenus.Genus

/-! # Bounded edge-insertion search from a connected spanning prefix -/

@[expose] public section

namespace MultiGenus

open Rotations Faces

/-- Reordering input edges preserves the independently specified rotation systems. -/
theorem legal_perm {n : Nat} {es fs : List Edge} {r : Rows} (hp : es.Perm fs) :
    Legal n es r ↔ Legal n fs r := by
  have h (v : Nat) : (neighbors es v).Perm (neighbors fs v) := hp.flatMap_right _
  exact and_congr_right fun _ => ⟨fun hr v hv => (hr v hv).trans (h v),
    fun hr v hv => (hr v hv).trans (h v).symm⟩

/-- A sublist of a simple input represents a simple subgraph on the same vertices. -/
theorem SimpleInput.sublist {n : Nat} {es fs : List Edge} (G : SimpleInput n es)
    (h : fs.Sublist es) : SimpleInput n fs :=
  ⟨fun e m => G.ordered e (h.subset m), fun e m => G.bounded e (h.subset m), h.nodup G.nodup⟩

/-- Reordering a simple input preserves its input conditions. -/
theorem SimpleInput.perm {n : Nat} {es fs : List Edge} (G : SimpleInput n es)
    (h : es.Perm fs) : SimpleInput n fs :=
  ⟨fun e m => G.ordered e (h.mem_iff.mpr m), fun e m => G.bounded e (h.mem_iff.mpr m),
    h.nodup_iff.mp G.nodup⟩

/-- Adding edges to a connected spanning subgraph preserves connectivity. -/
theorem connected_append {n : Nat} {es : List Edge} (h : ConnectedInput n es) (fs : List Edge) :
    ConnectedInput n (es ++ fs) := by
  refine ⟨h.1, fun u hu v hv => Relation.ReflTransGen.mono ?_ u v (h.2 u hu v hv)⟩
  intro a b adj
  exact mem_neighbors.mpr ((mem_neighbors.mp adj).imp (List.mem_append_left _)
    (List.mem_append_left _))

namespace Backtrack

/-- Every incidence order obtainable from a partial rotation by adding the given edges. -/
def Completes (r : Rows) : List Edge → Rows → Prop
  | [], s => s = r
  | e :: es, s => ∃ u ∈ insertEdge r e, Completes u es s

/-- With all spanning-prefix rotations as seeds, the leaves are exactly all legal rotations. -/
theorem complete_iff {n : Nat} (pre rest : List Edge) (s : Rows) :
    (∃ r, Legal n pre r ∧ Completes r rest s) ↔ Legal n (pre ++ rest) s := by
  induction rest generalizing pre with
  | nil => simp [Completes]
  | cons e es ih =>
    rw [show pre ++ e :: es = (pre ++ [e]) ++ es by simp, ← ih]
    constructor
    · rintro ⟨r, hr, u, hu, hs⟩
      exact ⟨u, legal_insertEdge hr hu, hs⟩
    · rintro ⟨u, hu, hs⟩
      obtain ⟨r, hr, hru⟩ := (edge_spec n pre e u).mpr hu
      exact ⟨r, hr, u, hru, hs⟩

private theorem prefix_step {n : Nat} {pre rest : List Edge} {e : Edge}
    (G : SimpleInput n (pre ++ e :: rest)) : SimpleInput n (pre ++ [e]) :=
  G.sublist ((List.Sublist.cons_cons e (List.nil_sublist rest)).append_left pre)

/-- Inserting a non-tree edge preserves genus or raises it by one. -/
theorem genus_insert {n : Nat} {pre : List Edge} {e : Edge} {r s : Rows}
    (G : SimpleInput n (pre ++ [e])) (con : ConnectedInput n pre) (hr : Legal n pre r)
    (hs : s ∈ insertEdge r e) :
    genusOf n (pre.length + 1) s = genusOf n pre.length r ∨
      genusOf n (pre.length + 1) s = genusOf n pre.length r + 1 := by
  have base := euler_genus (G.sublist (List.sublist_append_left ..)) con hr
  rcases Extension.faceCount_insertEdge G con hr hs with h | h <;> unfold genusOf at * <;> omega

/-- No completion can recover a genus below that of a connected spanning prefix. -/
theorem genus_le_completion {n : Nat} {pre rest : List Edge} {r s : Rows}
    (G : SimpleInput n (pre ++ rest)) (con : ConnectedInput n pre) (hr : Legal n pre r)
    (hs : Completes r rest s) : genusOf n pre.length r ≤ genusOf n (pre ++ rest).length s := by
  induction rest generalizing pre r with
  | nil => obtain rfl := hs; simp
  | cons e es ih =>
    obtain ⟨u, hu, hs⟩ := hs
    have hstep := genus_insert (prefix_step G) con hr hu
    have tail := ih (pre := pre ++ [e]) (by simpa using G) (connected_append con [e])
      (legal_insertEdge hr hu) hs
    apply Nat.le_trans (m := genusOf n (pre.length + 1) u) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

/-- Depth-first search for an embedding of exactly `target` handles. A prefix above the
budget is discarded before any further pairs of insertion slots are visited. -/
def branch (n target m : Nat) (r : Rows) : List Edge → Option Rows
  | [] => if genusOf n m r = target then some r else none
  | e :: es => if target < genusOf n m r then none else
      (insertEdge r e).findSome? (fun s => branch n target (m + 1) s es)

/-- A successful branch returns a completion of its seed at the exact target genus. -/
theorem branch_some {n t m : Nat} {r s : Rows} {es : List Edge}
    (h : branch n t m r es = some s) : Completes r es s ∧ genusOf n (m + es.length) s = t := by
  induction es generalizing m r with
  | nil =>
    simp only [branch] at h
    split at h <;> simp_all [Completes]
  | cons e es ih =>
    simp only [branch] at h
    split at h
    · contradiction
    · obtain ⟨u, hu, found⟩ := List.exists_of_findSome?_eq_some h
      obtain ⟨hs, hg⟩ := ih found
      exact ⟨⟨u, hu, hs⟩, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg⟩

/-- Bounded DFS finds a witness whenever this legal connected seed has a target completion. -/
theorem branch_finds {n t : Nat} {pre rest : List Edge} {r s : Rows}
    (G : SimpleInput n (pre ++ rest)) (con : ConnectedInput n pre) (hr : Legal n pre r)
    (hs : Completes r rest s) (hg : genusOf n (pre ++ rest).length s = t) :
    (branch n t pre.length r rest).isSome := by
  induction rest generalizing pre r with
  | nil => obtain rfl := hs; simpa [branch] using hg
  | cons e es ih =>
    have le := genus_le_completion G con hr hs
    rw [hg] at le
    simp only [branch, Nat.not_lt.mpr le, ite_false, List.findSome?_isSome_iff]
    obtain ⟨u, hu, us⟩ := hs
    refine ⟨u, hu, ?_⟩
    simpa using ih (pre := pre ++ [e]) (by simpa using G) (connected_append con [e])
      (legal_insertEdge hr hu) us (by simpa using hg)

/-- Visit the rotations of a growing tree depth first, stopping as soon as a seed's
continuation succeeds. Only the current insertion choices need to be stored. -/
def visitSeeds (finish : Rows → Option Rows) : List Edge → Rows → Option Rows
  | [], r => finish r
  | e :: es, r => (insertEdge r e).findSome? (visitSeeds finish es)

private theorem first_flatMap {A B C : Type*} (xs : List A) (choices : A → List B)
    (f : B → Option C) : (xs.flatMap choices).findSome? f =
      xs.findSome? (fun x => (choices x).findSome? f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.findSome?_append, ih, List.findSome?_cons]
    cases (choices a).findSome? f <;> rfl

private theorem visitSeeds_eq (finish : Rows → Option Rows) (es : List Edge) (rs : List Rows) :
    (extend rs es).findSome? finish = rs.findSome? (visitSeeds finish es) := by
  induction es generalizing rs with
  | nil => rfl
  | cons e es ih =>
    change (extend _ es).findSome? finish = _
    rw [ih, first_flatMap]
    rfl

/-- Search all rotations of the chosen spanning prefix and return the first completed witness. -/
def exactFrom (n target : Nat) (pre rest : List Edge) : Option Rows :=
  visitSeeds (fun r => branch n target pre.length r rest) pre (List.replicate n [])

private theorem exactFrom_eq (n t : Nat) (pre rest : List Edge) : exactFrom n t pre rest =
    (enumerate n pre).findSome? (fun r => branch n t pre.length r rest) := by
  simp [exactFrom, enumerate, visitSeeds_eq]

/-- Every successful search returns a rotation of the input graph with the requested genus. -/
theorem exactFrom_sound {n t : Nat} {pre rest : List Edge} {r : Rows}
    (h : exactFrom n t pre rest = some r) : Legal n (pre ++ rest) r ∧
      genusOf n (pre ++ rest).length r = t := by
  rw [exactFrom_eq] at h
  obtain ⟨u, hu, found⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨hs, hg⟩ := branch_some found
  exact ⟨(complete_iff ..).mp ⟨_, (mem_enumerate_iff ..).mp hu, hs⟩, by simpa using hg⟩

/-- The budgeted edge-insertion search succeeds exactly at the realizable genera. -/
theorem exactFrom_iff {n t : Nat} {pre rest : List Edge} (G : SimpleInput n (pre ++ rest))
    (con : ConnectedInput n pre) :
    (exactFrom n t pre rest).isSome ↔ Realizes n (pre ++ rest) t := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨legal, eq⟩ := exactFrom_sound hr
    exact ⟨r, legal, eq ▸ euler_genus G (connected_append con rest) legal⟩
  · rintro ⟨r, legal, formula⟩
    obtain ⟨u, hu, hs⟩ := (complete_iff ..).mpr legal
    have eq := euler_genus G (connected_append con rest) legal
    rw [exactFrom_eq]
    apply List.findSome?_isSome_iff.mpr
    exact ⟨u, (mem_enumerate_iff ..).mpr hu, branch_finds G con hu hs (by omega)⟩

end Backtrack
end MultiGenus
