/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Darts
public import MultiGenus.Euler

/-! # The orientable genus of a connected rotation system -/

@[expose] public section

namespace MultiGenus

open Rotations Faces

/-- Euler genus calculation for a connected orientable rotation with `v` vertices and `e` edges. -/
def genusOf (v e : Nat) (rows : Rows) : Nat := (2 + e - v - faceCount rows) / 2

/-- A genus is realized by choosing cyclic orders at the vertices and counting facial orbits. -/
def Realizes (n : Nat) (edges : List Edge) (g : Nat) : Prop :=
  ∃ rows, Legal n edges rows ∧ 2 + edges.length = n + faceCount rows + 2 * g

/-- Euler's formula is exact on every legal rotation of a connected simple graph.
In particular, the division in `genusOf` always has a nonnegative even numerator. -/
theorem euler_genus {n : Nat} {edges : List Edge} {rows : Rows} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (h : Legal n edges rows) :
    2 + edges.length = n + faceCount rows + 2 * genusOf n edges.length rows := by
  by_cases small : n ≤ 1
  · have hn : n = 1 := by have := con.1; omega
    subst n
    have he : edges = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e em
      have := G.ordered e em
      have := G.bounded e em
      omega
    subst edges
    obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_pos (by rw [h.1]; decide)
    have nil : rs = [] := by have len := h.1; simpa using len
    subst rs
    have hr := h.2 0 (by decide)
    have : r = [] := by simpa [neighbors] using hr
    subst r
    decide
  · have hn : 1 < n := by omega
    let : Nonempty (Dart rows) :=
      ⟨(Map.origin_surjective h con hn (⟨0, con.1⟩ : Fin n)).choose⟩
    obtain ⟨g, genus⟩ := Euler.exists_genus (rho rows) (Map.pairs G h)
      (Map.pairs_distinct G h) (Map.connected G h con)
    have many : rows ≠ [[]] := by
      intro e
      have len := h.1
      rw [e] at len
      change 1 = n at len
      omega
    rw [Map.fold_pairs, Surgery.countCycles, Map.vertex_cycles G h con hn] at genus
    have faces := faceCount_eq (valid_of_legal G h)
    simp only [many, ite_false] at faces
    change 2 + (Map.pairs G h).length = n + Nat.card _ + 2 * g at genus
    rw [← faces] at genus
    simp only [Map.pairs, List.length_map, List.length_attach] at genus
    unfold genusOf
    omega

end MultiGenus
