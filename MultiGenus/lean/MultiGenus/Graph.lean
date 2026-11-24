/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Rotations
public import Mathlib.Logic.Relation
import Mathlib.Data.List.Perm.Basic

/-! # Graph inputs for orientable genus search -/

@[expose] public section

namespace MultiGenus

open Rotations

/-- A simple undirected graph on `0, ..., n-1`. Store each edge once, smaller endpoint first. -/
structure SimpleInput (n : Nat) (edges : List Edge) : Prop where
  /-- The smaller endpoint is strictly below the larger one. -/
  ordered : ∀ e ∈ edges, e.1 < e.2
  /-- Both endpoints belong to the vertex set. -/
  bounded : ∀ e ∈ edges, e.2 < n
  /-- No undirected edge is repeated. -/
  nodup : edges.Nodup

/-- The vertex set is nonempty and edges give paths between every two vertices. -/
def ConnectedInput (n : Nat) (edges : List Edge) : Prop :=
  0 < n ∧ ∀ u < n, ∀ v < n,
    Relation.ReflTransGen (fun a b => b ∈ neighbors edges a) u v

/-- An incidence is present precisely when the input contains that edge in either orientation. -/
theorem mem_neighbors {edges : List Edge} {u v : Nat} :
    v ∈ neighbors edges u ↔ (u,v) ∈ edges ∨ (v,u) ∈ edges := by
  simp only [neighbors, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨⟨a,b⟩, h, h₁ | h₂⟩
    · split at h₁ <;> simp_all
    · split at h₂ <;> simp_all
  · rintro (h | h)
    · exact ⟨_, h, Or.inl (by simp)⟩
    · exact ⟨_, h, Or.inr (by simp)⟩

namespace SimpleInput

variable {n : Nat} {edges : List Edge} (G : SimpleInput n edges)

include G

/-- A neighbor of any vertex is in range. -/
theorem neighbor_lt {u v : Nat} (h : v ∈ neighbors edges u) : v < n := by
  rcases mem_neighbors.mp h with h | h
  · exact G.bounded _ h
  · exact Nat.lt_trans (G.ordered _ h) (G.bounded _ h)

/-- A simple input has one incidence per neighbor at each vertex. -/
theorem neighbors_nodup (u : Nat) : (neighbors edges u).Nodup := by
  induction edges with
  | nil => simp [neighbors]
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    have ab : a < b := G.ordered _ (.head _)
    have fresh := (List.nodup_cons.mp G.nodup).1
    have tail : SimpleInput n es := ⟨fun e h => G.ordered e (.tail _ h),
      fun e h => G.bounded e (.tail _ h), (List.nodup_cons.mp G.nodup).2⟩
    have ns := ih tail
    change (((if a = u then [b] else []) ++ (if b = u then [a] else [])) ++
      neighbors es u).Nodup
    have back : (b,a) ∉ es := fun h => (Nat.lt_asymm ab (tail.ordered _ h))
    by_cases ha : a = u <;> by_cases hb : b = u <;> simp_all [mem_neighbors]

omit G

/-- In a connected graph of order at least two, every vertex has a dart. -/
theorem exists_neighbor (con : ConnectedInput n edges) (hn : 1 < n) (u : Nat) (hu : u < n) :
    ∃ v, v ∈ neighbors edges u := by
  let w := if u = 0 then 1 else 0
  have hw : w < n := by dsimp [w]; split <;> omega
  have ne : u ≠ w := by dsimp [w]; split <;> omega
  rcases (con.2 u hu w hw).cases_head with eq | ⟨v, h, _⟩
  · exact (ne eq).elim
  · exact ⟨v, h⟩

end SimpleInput
end MultiGenus
