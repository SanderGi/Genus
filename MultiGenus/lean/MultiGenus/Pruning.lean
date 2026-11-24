/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Backtrack
import Mathlib.Data.List.GetD

/-! # Common-face pruning for a connected spanning partial rotation -/

@[expose] public section

namespace MultiGenus.Pruning

open Faces Rotations Backtrack

/-- A face contains both endpoints if some corners at those vertices are on the same dart orbit. -/
def CommonFace {rows : Rows} (h : Valid rows) (e : Edge) : Prop :=
  ∃ a b : Dart rows, a.val.1 = e.1 ∧ b.val.1 = e.2 ∧ (facePerm h).SameCycle a b

/-- The vertex bitset of a face, obtained by projecting its bounded facial walk. -/
def faceVertices (rows : Rows) (d : Edge) : Finset Nat := (faceWalk rows d).image Prod.fst

private theorem mem_faceVertices {rows : Rows} (h : Valid rows) (d : Dart rows) (v : Nat) :
    v ∈ faceVertices rows d.val ↔ ∃ a : Dart rows, a.val.1 = v ∧ (facePerm h).SameCycle d a := by
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, rfl, ha⟩ := (mem_faceWalk h d x).mp hx
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact Finset.mem_image_of_mem _ ((mem_faceWalk h d a.val).mpr ⟨a, rfl, ha⟩)

/-- The C bitset test may scan all faces for one containing both endpoint vertices. -/
theorem commonFace_iff_faceVertices {rows : Rows} (h : Valid rows) (e : Edge) :
    CommonFace h e ↔ ∃ d : Dart rows, e.1 ∈ faceVertices rows d.val ∧
      e.2 ∈ faceVertices rows d.val := by
  constructor
  · rintro ⟨a, b, ha, hb, same⟩
    exact ⟨a, (mem_faceVertices h ..).mpr ⟨a, ha, .rfl⟩,
      (mem_faceVertices h ..).mpr ⟨b, hb, same⟩⟩
  · rintro ⟨d, hu, hv⟩
    obtain ⟨a, ha, hda⟩ := (mem_faceVertices h ..).mp hu
    obtain ⟨b, hb, hdb⟩ := (mem_faceVertices h ..).mp hv
    exact ⟨a, b, ha, hb, hda.symm.trans hdb⟩

/-- The two faces of a triangle have different dart sets and identical vertex bitsets. -/
theorem triangle_faces_share_vertex_set :
    let rows : Rows := [[1, 2], [0, 2], [0, 1]]
    faceWalk rows (0, 1) ≠ faceWalk rows (1, 0) ∧
      faceVertices rows (0, 1) = faceVertices rows (1, 0) := by decide

/-- Every placement of an edge whose endpoints share no face uses exactly one more handle. -/
theorem genus_insert_of_no_commonFace {n pre e r s} (G : SimpleInput n (pre ++ [e]))
    (con : ConnectedInput n pre) (hr : Legal n pre r)
    (apart : ¬ CommonFace (valid_of_legal (Extension.simple_prefix G) hr) e)
    (child : s ∈ insertEdge r e) : genusOf n (pre.length + 1) s = genusOf n pre.length r + 1 := by
  obtain ⟨a, b, ha, hb, _, _, _, merge⟩ := Extension.faceCount_insertEdge_corners G con hr child
  have faces := merge fun hs => apart ⟨a, b, ha, hb, hs⟩
  have old := euler_genus (Extension.simple_prefix G) con hr
  have new := euler_genus G (connected_append con [e]) (legal_insertEdge hr child)
  simp only [List.length_append, List.length_singleton] at new
  omega

/-- With this edge next, every completion exceeds the current genus budget. -/
theorem genus_lt_completion_cons {n pre e rest r s} (G : SimpleInput n (pre ++ e :: rest))
    (con : ConnectedInput n pre) (hr : Legal n pre r)
    (apart : ¬ CommonFace (valid_of_legal (Extension.simple_prefix G) hr) e)
    (done : Completes r (e :: rest) s) :
    genusOf n pre.length r < genusOf n (pre ++ e :: rest).length s := by
  obtain ⟨u, child, tail⟩ := done
  have G₁ := G.sublist ((List.Sublist.cons_cons e (List.nil_sublist rest)).append_left pre)
  have step := genus_insert_of_no_commonFace G₁ con hr apart child
  have bound := genus_le_completion (pre := pre ++ [e]) (by simpa using G)
    (connected_append con [e]) (legal_insertEdge hr child) tail
  simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_nil,
    List.length_cons, Nat.zero_add] at bound ⊢
  omega

private theorem sublist_slot {xs ys : List Nat} {a : Nat} (hs : ys ∈ slots a xs) :
    xs.Sublist ys := by
  induction xs generalizing ys with
  | nil => exact List.nil_sublist _
  | cons x xs ih =>
    simp only [slots, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨zs, hz, rfl⟩
    · exact (List.Sublist.refl _).cons _
    · exact (ih hz).cons_cons _

private theorem sublist_insertNeighbor {r s : Rows} {u a : Nat} (hs : s ∈ insertNeighbor u a r)
    (v : Nat) : (row r v).Sublist (row s v) := by
  induction r generalizing s u v with
  | nil => exact List.nil_sublist _
  | cons x xs ih =>
    cases u with
    | zero =>
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hs
      cases v with
      | zero => exact sublist_slot hy
      | succ _ => exact .refl _
    | succ u =>
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hs
      cases v with
      | zero => exact .refl _
      | succ v => exact ih hy v

private theorem sublist_of_completes {r s : Rows} {es : List Edge} (h : Completes r es s)
    (v : Nat) : (row r v).Sublist (row s v) := by
  induction es generalizing r with
  | nil => obtain rfl := h; exact .refl _
  | cons e es ih =>
    obtain ⟨u, hu, tail⟩ := h
    obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp hu
    exact (sublist_insertNeighbor ht v).trans ((sublist_insertNeighbor hu v).trans (ih tail))

/-- A completed row restricted to the prefix neighbors recovers the exact starting row. -/
theorem row_filter_of_completes {n pre rest r s} (G : SimpleInput n (pre ++ rest))
    (hr : Legal n pre r) (done : Completes r rest s) {v : Nat} (hv : v < n) :
    ((row s v).filter fun x => x ∈ neighbors pre v) = row r v := by
  let keep (x : Nat) := decide (x ∈ neighbors pre v)
  have sub := sublist_of_completes done v
  have mem {x : Nat} : x ∈ row r v ↔ x ∈ neighbors pre v := (hr.2 v hv).mem_iff
  have fixed : (row r v).filter keep = row r v :=
    List.filter_eq_self.mpr fun x hx => decide_eq_true (mem.mp hx)
  have inc := sub.filter keep
  rw [fixed] at inc
  have legal := (complete_iff pre rest s).mp ⟨r, hr, done⟩
  have nd := (valid_of_legal G legal).nodup v
  have perm : ((row s v).filter keep).Perm (row r v) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (nd.filter _) (nd.sublist sub)
    ext x
    simp only [List.mem_toFinset, List.mem_filter, keep, decide_eq_true_eq, ← mem,
      and_iff_right_iff_imp]
    exact fun hx => sub.subset hx
  exact (inc.eq_of_length perm.length_eq.symm).symm

/-- Reordering missing edges preserves the completions of each fixed partial rotation,
including the exact linear starting point of each row. -/
theorem completes_of_perm {n pre rest rest' r s} (G : SimpleInput n (pre ++ rest))
    (hr : Legal n pre r) (order : rest.Perm rest') (done : Completes r rest s) :
    Completes r rest' s := by
  have perm := order.append_left pre
  have legal := (legal_perm perm).mp ((complete_iff pre rest s).mp ⟨r, hr, done⟩)
  obtain ⟨t, ht, path⟩ := (complete_iff pre rest' s).mpr legal
  have eq : r = t := by
    apply List.ext_getElem (hr.1.trans ht.1.symm)
    intro v hvr hvt
    have hv := hr.1 ▸ hvr
    have eqrow := (row_filter_of_completes G hr done hv).symm.trans
      (row_filter_of_completes (G.perm perm) ht path hv)
    simpa only [row, List.getD_eq_getElem r [] hvr, List.getD_eq_getElem t [] hvt] using eqrow
  exact eq ▸ path

/-- An edge with no common face anywhere in the remaining list forces a handle in every completion.
This justifies the common-face scan at the current budget independently of the search order. -/
theorem genus_lt_completion_of_no_commonFace {n pre rest r s e}
    (G : SimpleInput n (pre ++ rest)) (con : ConnectedInput n pre) (hr : Legal n pre r)
    (he : e ∈ rest) (apart : ¬ CommonFace (valid_of_legal (Extension.simple_prefix G) hr) e)
    (done : Completes r rest s) : genusOf n pre.length r < genusOf n (pre ++ rest).length s := by
  have order := List.perm_cons_erase he
  have perm := order.append_left pre
  have bound := genus_lt_completion_cons (G.perm perm) con hr apart
    (completes_of_perm G hr order done)
  rwa [← perm.length_eq] at bound

/-- Once the budget is exhausted, one remaining edge with no common face prunes the branch. -/
theorem no_completion_within_budget {n pre rest r e budget}
    (G : SimpleInput n (pre ++ rest)) (con : ConnectedInput n pre) (hr : Legal n pre r)
    (he : e ∈ rest) (apart : ¬ CommonFace (valid_of_legal (Extension.simple_prefix G) hr) e)
    (spent : budget ≤ genusOf n pre.length r) :
    ¬ ∃ s, Completes r rest s ∧ genusOf n (pre ++ rest).length s ≤ budget := by
  rintro ⟨s, done, within⟩
  exact (genus_lt_completion_of_no_commonFace G con hr he apart done).not_ge (within.trans spent)

end MultiGenus.Pruning
