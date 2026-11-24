/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Rotations
public import Mathlib.GroupTheory.Perm.List

/-! # Endpoint rows and cyclic successors after insertion into a slot -/

public section

namespace MultiGenus.Rotations

private theorem neighbor_rows {rs rs' : Rows} {u z : Nat}
    (h : rs' ∈ insertNeighbor u z rs) :
    rs'.length = rs.length ∧
      (u < rs.length → rs'.getD u [] ∈ slots z (rs.getD u [])) ∧
      ∀ w, w ≠ u → rs'.getD w [] = rs.getD w [] := by
  induction rs generalizing rs' u with
  | nil =>
    simp only [insertNeighbor, List.mem_singleton] at h
    subst rs'
    simp
  | cons r rs ih =>
    cases u with
    | zero =>
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
      refine ⟨rfl, fun _ => hs, ?_⟩
      rintro (_ | w) ne
      · exact (ne rfl).elim
      · rfl
    | succ u =>
      obtain ⟨ss, hs, rfl⟩ := List.mem_map.mp h
      obtain ⟨hlen, hslot, hrest⟩ := ih hs
      refine ⟨by simp [hlen], fun hu => hslot (Nat.lt_of_succ_lt_succ hu), ?_⟩
      rintro (_ | w) ne
      · rfl
      · exact hrest w (fun h => ne (congrArg Nat.succ h))

/-- Inserting an edge changes its two endpoint rows by one slot insertion apiece.
Every other vertex has exactly its old row, including out-of-range lookups. -/
theorem insertEdge_rows {rs rs' : Rows} {u v : Nat} (huv : u ≠ v)
    (hu : u < rs.length) (hv : v < rs.length) (h : rs' ∈ insertEdge rs (u, v)) :
    rs'.getD u [] ∈ slots v (rs.getD u []) ∧
    rs'.getD v [] ∈ slots u (rs.getD v []) ∧
    ∀ w, w ≠ u → w ≠ v → rs'.getD w [] = rs.getD w [] := by
  obtain ⟨ss, hs, h'⟩ := List.mem_flatMap.mp h
  obtain ⟨hlen, hsu, hrest⟩ := neighbor_rows hs
  obtain ⟨_, hsv, hrest'⟩ := neighbor_rows h'
  exact ⟨hrest' u huv ▸ hsu hu, hrest v huv.symm ▸ hsv (hlen ▸ hv),
    fun w wu wv => (hrest' w wv).trans (hrest w wu)⟩

private theorem split_slot {xs ys : List Nat} {z : Nat} (h : ys ∈ slots z xs) :
    ∃ l r, xs = l ++ r ∧ ys = l ++ z :: r := by
  induction xs generalizing ys with
  | nil =>
    simp only [slots, List.mem_singleton] at h
    exact ⟨[], [], rfl, h⟩
  | cons x xs ih =>
    simp only [slots, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨zs, hz, rfl⟩
    · exact ⟨[], _, rfl, rfl⟩
    · obtain ⟨l, r, rfl, rfl⟩ := ih hz
      exact ⟨x :: l, r, rfl, rfl⟩

private theorem rotate_cut (l r : List Nat) (hd : (l ++ r).Nodup) :
    (l ++ r).formPerm = (r ++ l).formPerm :=
  List.formPerm_eq_of_isRotated hd ⟨l.length, List.rotate_append_length_eq l r⟩

/-- In a nonempty cyclic row, inserting a fresh neighbor exchanges it with the old
successor of its chosen slot in the successor permutation. -/
theorem slots_formPerm {xs ys : List Nat} {z : Nat} (hne : xs ≠ []) (hd : xs.Nodup)
    (hz : z ∉ xs) (h : ys ∈ slots z xs) :
    ∃ k ∈ xs, ys.formPerm = Equiv.swap z k * xs.formPerm := by
  obtain ⟨l, r, rfl, rfl⟩ := split_slot h
  have nd : (l ++ z :: r).Nodup :=
    List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨hz, hd⟩)
  have new := rotate_cut l (z :: r) nd
  have old := rotate_cut l r hd
  rw [new, old]
  cases he : r ++ l with
  | nil => simp_all
  | cons k tail =>
    refine ⟨k, ?_, ?_⟩
    · exact List.perm_append_comm.mem_iff.mp (he ▸ List.mem_cons_self)
    · change (z :: (r ++ l)).formPerm = _
      rw [he, List.formPerm_cons_cons]

end MultiGenus.Rotations
