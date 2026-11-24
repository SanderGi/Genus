/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Genus
public import MultiGenus.SurgerySubdivide
import Mathlib.Data.List.Permutation

/-!
# Global reflection and the orientation of the initial tree

Reversing every neighbor row reverses every facial walk after reversing its darts.
In `get_initial_embedding`, three distinguished neighbors of the root fix one of
two cyclic orders. Restricting a completed row to those neighbors records the
orientation even after the remaining edges have been inserted.
-/

@[expose] public section

namespace MultiGenus.Reflection

open Faces Rotations

/-- Reflect every local rotation. -/
def mirror (rows : Rows) : Rows := rows.map List.reverse

@[simp] theorem length_mirror (rows : Rows) : (mirror rows).length = rows.length := by
  simp [mirror]

@[simp] theorem mirror_mirror (rows : Rows) : mirror (mirror rows) = rows := by
  simp [mirror]

@[simp] theorem row_mirror (rows : Rows) (v : Nat) :
    row (mirror rows) v = (row rows v).reverse := by
  induction rows generalizing v with
  | nil => cases v <;> rfl
  | cons r rs ih => cases v with
    | zero => rfl
    | succ v => exact ih v

/-- Reflection preserves every vertex's neighbor multiset. -/
theorem legal_mirror {n edges rows} (h : Legal n edges rows) : Legal n edges (mirror rows) := by
  refine ⟨(length_mirror rows).trans h.1, fun v hv => ?_⟩
  change (row (mirror rows) v).Perm _
  rw [row_mirror]
  exact (List.reverse_perm _).trans (h.2 v hv)

/-- All dart validity conditions are invariant under reflection. -/
theorem valid_mirror {rows} (h : Valid rows) : Valid (mirror rows) where
  bounded hv := by simpa using h.bounded (by simpa using hv)
  symmetric hv := by simpa using h.symmetric (by simpa using hv)
  nodup v := by simpa using h.nodup v

@[simp] theorem darts_mirror (rows : Rows) : darts (mirror rows) = darts rows := by
  ext ⟨u, v⟩
  simp

/-- The correspondence of facial walks reverses the direction of each dart. -/
def reverseDart {rows} (h : Valid rows) : Dart rows ≃ Dart (mirror rows) where
  toFun d := ⟨(alpha h d).val, by rw [darts_mirror]; exact (alpha h d).prop⟩
  invFun d := ⟨(alpha (valid_mirror h) d).val, by
    rw [← darts_mirror rows]
    exact (alpha (valid_mirror h) d).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- One backwards facial step becomes one forwards step in the reflected embedding. -/
theorem reverseDart_facePerm_inv {rows} (h : Valid rows) (d : Dart rows) :
    reverseDart h ((facePerm h)⁻¹ d) = facePerm (valid_mirror h) (reverseDart h d) := by
  apply Subtype.ext
  change (_, (row rows d.val.1).formPerm.symm d.val.2) =
    (_, (row (mirror rows) d.val.1).formPerm d.val.2)
  rw [row_mirror, List.formPerm_reverse]
  rfl

/-- Reflection preserves the number of face orbits computed by the dart walker. -/
theorem orbitCount_mirror {rows} (h : Valid rows) : orbitCount (mirror rows) = orbitCount rows := by
  rw [orbitCount_eq (valid_mirror h), orbitCount_eq h]
  exact (Surgery.countCycles_congr (reverseDart h) _ _ (reverseDart_facePerm_inv h)).symm.trans
    (Surgery.countCycles_inv _)

/-- Reflection preserves the executable face count, including the isolated vertex. -/
theorem faceCount_mirror {rows} (h : Valid rows) : faceCount (mirror rows) = faceCount rows := by
  have iso : mirror rows = [[]] ↔ rows = [[]] := ⟨fun e => by
    calc rows = mirror (mirror rows) := (mirror_mirror rows).symm
         _ = mirror [[]] := congrArg mirror e
         _ = [[]] := rfl, by rintro rfl; rfl⟩
  simp only [faceCount, iso, orbitCount_mirror h]

/-- The genus computed from Euler's formula is unchanged by reflection. -/
theorem genusOf_mirror {rows} (h : Valid rows) (v e : Nat) :
    genusOf v e (mirror rows) = genusOf v e rows := by
  simp only [genusOf, faceCount_mirror h]

/-- Restrict a neighbor row to the three edges used to orient the root. -/
def tripleRow (r : List Nat) (a b c : Nat) : List Nat :=
  r.filter fun x => x ∈ [a, b, c]

/-- The distinguished neighbors occur in the cyclic order `a, b, c` at the root. -/
def RootOrder (rows : Rows) (root a b c : Nat) : Prop :=
  [a, b, c].IsRotated (tripleRow (row rows root) a b c)

private theorem filter_perm {r s : List Nat} (nd : r.Nodup) (ns : s.Nodup)
    (incl : ∀ x ∈ s, x ∈ r) : (r.filter fun x => x ∈ s).Perm s := by
  apply List.perm_of_nodup_nodup_toFinset_eq (nd.filter _) ns
  ext x
  simpa only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    using incl x

private theorem rotated_three {a b c : Nat} {r : List Nat} :
    [a, b, c].IsRotated r ↔ r = [a, b, c] ∨ r = [b, c, a] ∨ r = [c, a, b] := by
  rw [List.isRotated_iff_mem_map_range]
  rw [show List.range ([a, b, c].length + 1) = [0, 1, 2, 3] by rfl]
  simp [List.rotate_cons_succ, or_comm, or_left_comm]

private theorem triple_or_reverse {r : List Nat} {a b c : Nat} (h : r.Perm [a, b, c])
    (distinct : [a, b, c].Nodup) :
    [a, b, c].IsRotated r.reverse ↔ ¬ [a, b, c].IsRotated r := by
  have mem := List.mem_permutations'.mpr h
  simp only [List.permutations', List.flatMap_cons, List.permutations'Aux, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at mem
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  obtain ⟨⟨hab, hac⟩, hbc, _⟩ := distinct
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rotated_three, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- Exactly one member of a mirror pair has the prescribed orientation of the root triple. -/
theorem rootOrder_mirror_iff {rows root a b c} (h : Valid rows) (distinct : [a, b, c].Nodup)
    (ha : a ∈ row rows root) (hb : b ∈ row rows root) (hc : c ∈ row rows root) :
    RootOrder (mirror rows) root a b c ↔ ¬ RootOrder rows root a b c := by
  have incl (x : Nat) (hx : x ∈ [a, b, c]) : x ∈ row rows root := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  simpa only [RootOrder, row_mirror, tripleRow, List.filter_reverse] using
    triple_or_reverse (filter_perm (h.nodup root) distinct incl) distinct

/-- Fixing the initial root triple preserves every attainable genus of a simple graph. -/
theorem realizes_iff_rootOrder {n edges g root a b c} (G : SimpleInput n edges) (hr : root < n)
    (distinct : [a, b, c].Nodup) (ha : a ∈ neighbors edges root)
    (hb : b ∈ neighbors edges root) (hc : c ∈ neighbors edges root) :
    Realizes n edges g ↔ ∃ rows, Legal n edges rows ∧ RootOrder rows root a b c ∧
      2 + edges.length = n + faceCount rows + 2 * g := by
  constructor
  · rintro ⟨rows, legal, genus⟩
    by_cases oriented : RootOrder rows root a b c
    · exact ⟨rows, legal, oriented, genus⟩
    · have valid := valid_of_legal G legal
      have mem {x : Nat} : x ∈ row rows root ↔ x ∈ neighbors edges root :=
        (legal.2 root hr).mem_iff
      exact ⟨mirror rows, legal_mirror legal,
        (rootOrder_mirror_iff valid distinct (mem.mpr ha) (mem.mpr hb) (mem.mpr hc)).mpr oriented,
        by rwa [faceCount_mirror valid]⟩
  · rintro ⟨rows, legal, _, genus⟩
    exact ⟨rows, legal, genus⟩

/-- At degrees zero, one and two all permutations of the row give the same cyclic order. -/
theorem isRotated_of_length_le_two {r s : List Nat} (perm : r.Perm s) (degree : s.length ≤ 2) :
    s.IsRotated r := by
  have mem := List.mem_permutations'.mpr perm
  match s with
  | [] => obtain rfl := List.perm_nil.mp perm; exact .refl _
  | [a] =>
    have e : r = [a] := by simpa [List.permutations', List.permutations'Aux] using mem
    exact e ▸ .refl _
  | [a, b] =>
    have e : r = [a, b] ∨ r = [b, a] := by
      simpa [List.permutations', List.permutations'Aux] using mem
    rcases e with rfl | rfl
    · exact .refl _
    · exact List.isRotated_append (l := [a]) (l' := [b])
  | _ :: _ :: _ :: _ => simp at degree

/-- A completed rotation induces the prescribed seed order at every seed vertex. -/
def AgreesWithSeed (seed rows : Rows) : Prop :=
  ∀ v < seed.length,
    (row seed v).IsRotated ((row rows v).filter fun x => x ∈ row seed v)

/-- The C initializer's degree-three root and its paths may all be fixed simultaneously.
Agreement tests the cyclic orders on the seed edges inside the completed rows. -/
theorem realizes_iff_agreesWithSeed {n edges g root a b c seed} (G : SimpleInput n edges)
    (valid : Valid seed) (len : seed.length = n) (hr : root < n)
    (triple : row seed root = [a, b, c]) (small : ∀ v < n, v ≠ root → (row seed v).length ≤ 2)
    (incl : ∀ v < n, ∀ x ∈ row seed v, x ∈ neighbors edges v) :
    Realizes n edges g ↔ ∃ rows, Legal n edges rows ∧ AgreesWithSeed seed rows ∧
      2 + edges.length = n + faceCount rows + 2 * g := by
  have nd := valid.nodup root
  rw [triple] at nd
  have sub := incl root hr
  rw [triple] at sub
  constructor
  · intro hg
    obtain ⟨rows, legal, oriented, genus⟩ := (realizes_iff_rootOrder G hr nd
      (sub a (by simp)) (sub b (by simp)) (sub c (by simp))).mp hg
    refine ⟨rows, legal, ?_, genus⟩
    intro v hv
    rw [len] at hv
    by_cases eq : v = root
    · subst v
      rw [triple]
      exact oriented
    · apply isRotated_of_length_le_two _ (small v hv eq)
      exact filter_perm ((valid_of_legal G legal).nodup v) (valid.nodup v)
        fun x hx => (legal.2 v hv).mem_iff.mpr (incl v hv x hx)
  · rintro ⟨rows, legal, _, genus⟩
    exact ⟨rows, legal, genus⟩

end MultiGenus.Reflection
