/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Graph
public import MultiGenus.Faces
import Mathlib.Data.List.Nodup

/-! # From graph incidence lists to a connected dart map -/

@[expose] public section

namespace MultiGenus

open Rotations Faces

variable {n : Nat} {edges : List Edge} {rows : Rows}

/-- A legal ordering of the incidences of a simple graph defines a dart permutation. -/
theorem valid_of_legal (G : SimpleInput n edges) (h : Legal n edges rows) : Valid rows := by
  have outside (u : Nat) (hu : ¬ u < n) : row rows u = [] := by
    have len := h.1
    simp [row, List.getD, List.getElem?_eq_none (by omega : rows.length ≤ u)]
  constructor
  · intro u v hv
    by_cases hu : u < n
    · rw [h.1]
      exact G.neighbor_lt ((h.2 u hu).mem_iff.mp hv)
    · simp [outside u hu] at hv
  · intro u v hv
    by_cases hu : u < n
    · have m := (h.2 u hu).mem_iff.mp hv
      apply (h.2 v (G.neighbor_lt m)).mem_iff.mpr
      exact mem_neighbors.mpr (mem_neighbors.mp m).symm
    · simp [outside u hu] at hv
  · intro u
    by_cases hu : u < n
    · exact (h.2 u hu).nodup_iff.mpr (G.neighbors_nodup u)
    · simp [outside u hu]

namespace Map

variable (G : SimpleInput n edges) (h : Legal n edges rows)

include G h in
/-- An input edge gives a dart in the chosen rotation. -/
theorem input_dart {a b : Nat} (hab : (a, b) ∈ edges) : (a, b) ∈ darts rows := by
  have ha := Nat.lt_trans (G.ordered _ hab) (G.bounded _ hab)
  exact mem_darts.mpr ⟨h.1 ▸ ha, (h.2 a ha).mem_iff.mpr (mem_neighbors.mpr (.inl hab))⟩

/-- The two opposite darts associated to an input edge. -/
def edgePair (e : {e // e ∈ edges}) : Dart rows × Dart rows :=
  let x : Dart rows := ⟨e.val, input_dart G h e.prop⟩
  (x, alpha (valid_of_legal G h) x)

/-- The edge reversal is a product of disjoint transpositions, one per input edge. -/
def pairs : List (Dart rows × Dart rows) := edges.attach.map (edgePair G h)

include h in
private theorem orientation (x : Dart rows) : x.val ∈ edges ∨ x.val.swap ∈ edges := by
  exact mem_neighbors.mp ((h.2 _ (h.1 ▸ (mem_darts.mp x.prop).1)).mem_iff.mp
    (mem_darts.mp x.prop).2)

private theorem edge_or_reverse (x : Dart rows) :
    ∃ e : {e // e ∈ edges}, x = (edgePair G h e).1 ∨ x = (edgePair G h e).2 := by
  rcases orientation h x with hx | hx
  · exact ⟨⟨_, hx⟩, Or.inl (Subtype.ext rfl)⟩
  · exact ⟨⟨_, hx⟩, Or.inr (Subtype.ext rfl)⟩

private theorem different_edges {a b : {e // e ∈ edges}} (ne : a ≠ b) :
    (edgePair G h a).1 ≠ (edgePair G h b).1 ∧
    (edgePair G h a).1 ≠ (edgePair G h b).2 ∧
    (edgePair G h a).2 ≠ (edgePair G h b).1 ∧
    (edgePair G h a).2 ≠ (edgePair G h b).2 := by
  have ha := G.ordered _ a.prop
  have hb := G.ordered _ b.prop
  have ff : a.val ≠ b.val := fun eq => ne (Subtype.ext eq)
  have fr : a.val ≠ b.val.swap := by
    intro eq
    have := congrArg Prod.fst eq
    have := congrArg Prod.snd eq
    dsimp at *; omega
  have rf : a.val.swap ≠ b.val := fun eq => fr (congrArg Prod.swap eq)
  exact ⟨fun eq => ff (congrArg (fun d : Dart rows => d.val) eq),
    fun eq => fr (congrArg (fun d : Dart rows => d.val) eq),
    fun eq => rf (congrArg (fun d : Dart rows => d.val) eq),
    fun eq => ff (congrArg (fun d : Dart rows => d.val.swap) eq)⟩

private theorem prod_at {A D : Type*} [DecidableEq A] (f : A → Equiv.Perm D) (k : A)
    (x y : D) (hit : f k x = y) (miss : ∀ a, a ≠ k → f a x = x ∧ f a y = y)
    (xs : List A) (nd : xs.Nodup) : (xs.map f).prod x = if k ∈ xs then y else x := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    obtain ⟨out, nd⟩ := List.nodup_cons.mp nd
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih nd]
    by_cases ha : a = k
    · subst a; simp [out, hit]
    · by_cases hk : k ∈ as <;> simp [Ne.symm ha, hk, (miss a ha).1, (miss a ha).2]

private theorem reversal_prod :
    ((pairs G h).map (fun e => Equiv.swap e.1 e.2)).prod = alpha (valid_of_legal G h) := by
  ext x : 1
  obtain ⟨k, hx⟩ := edge_or_reverse G h x
  let f (e : {e // e ∈ edges}) := Equiv.swap (edgePair G h e).1 (edgePair G h e).2
  let y := alpha (valid_of_legal G h) x
  have hit : f k x = y := by
    rcases hx with rfl | rfl
    · exact Equiv.swap_apply_left ..
    · exact Equiv.swap_apply_right ..
  have miss (a : {e // e ∈ edges}) (ha : a ≠ k) : f a x = x ∧ f a y = y := by
    obtain ⟨ff, fr, rf, rr⟩ := different_edges G h ha
    rcases hx with rfl | rfl
    · exact ⟨Equiv.swap_apply_of_ne_of_ne (Ne.symm ff) (Ne.symm rf),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm fr) (Ne.symm rr)⟩
    · exact ⟨Equiv.swap_apply_of_ne_of_ne (Ne.symm fr) (Ne.symm rr),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm ff) (Ne.symm rf)⟩
  simpa [pairs, List.map_map, f, y, Function.comp_def] using
    prod_at f k x y hit miss edges.attach G.nodup.attach

/-- Pair all the darts, then follow the cyclic successor at their new origin. -/
theorem fold_pairs : (pairs G h).foldl (fun p e => p * Equiv.swap e.1 e.2) (rho rows) =
    facePerm (valid_of_legal G h) := by
  rw [show facePerm (valid_of_legal G h) = rho rows * alpha (valid_of_legal G h) from rfl,
    ← reversal_prod G h]
  generalize pairs G h = ps
  generalize rho rows = p
  induction ps generalizing p with
  | nil => simp
  | cons a as ih => simp [ih, mul_assoc]

/-- A simple edge pairs two distinct darts. -/
theorem pairs_distinct (e : Dart rows × Dart rows) (he : e ∈ pairs G h) : e.1 ≠ e.2 := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  have lt := G.ordered _ a.prop
  intro eq
  exact (Nat.ne_of_lt lt) (congrArg (fun d : Dart rows => d.val.1) eq)

/-- Visiting darts by a vertex rotation and by crossing edges connects the full dart set. -/
theorem connected (con : ConnectedInput n edges) (q : Equiv.Perm (Dart rows))
    (localOrbits : ∀ x y, (rho rows).SameCycle x y → q.SameCycle x y)
    (cross : ∀ e ∈ pairs G h, q.SameCycle e.1 e.2) (x y : Dart rows) : q.SameCycle x y := by
  have local' (a b : Dart rows) (eq : a.val.1 = b.val.1) :=
    localOrbits a b ((rho_sameCycle_iff (valid_of_legal G h) a b).mpr eq)
  have across (a : Dart rows) : q.SameCycle a (alpha (valid_of_legal G h) a) := by
    obtain ⟨k, hk⟩ := edge_or_reverse G h a
    have kcross := cross (edgePair G h k) (List.mem_map.mpr ⟨k, List.mem_attach .., rfl⟩)
    rcases hk with rfl | rfl
    · exact kcross
    · exact kcross.symm
  have transport {u v : Nat} (path : Relation.ReflTransGen (fun a b => b ∈ neighbors edges a) u v) :
      ∀ a b : Dart rows, a.val.1 = u → b.val.1 = v → q.SameCycle a b := by
    induction path with
    | refl => exact fun a b ea eb => local' a b (ea.trans eb.symm)
    | @tail v w path edge ih =>
      intro a b ea eb
      have hv := G.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp edge).symm)
      let d : Dart rows := ⟨(v, w), mem_darts.mpr ⟨h.1 ▸ hv, (h.2 v hv).mem_iff.mpr edge⟩⟩
      exact ((ih a d ea rfl).trans (across d)).trans (local' _ b eb.symm)
  exact transport (con.2 _ (h.1 ▸ (mem_darts.mp x.prop).1) _ (h.1 ▸ (mem_darts.mp y.prop).1))
    x y rfl rfl

/-- All origins occur when the connected graph has two or more vertices. -/
theorem origin_surjective (con : ConnectedInput n edges) (hn : 1 < n) :
    Function.Surjective (fun x : Dart rows =>
      (⟨x.val.1, h.1 ▸ (mem_darts.mp x.prop).1⟩ : Fin n)) := by
  intro u
  obtain ⟨v, hv⟩ := SimpleInput.exists_neighbor con hn u u.isLt
  exact ⟨⟨(u, v), mem_darts.mpr ⟨h.1 ▸ u.isLt, (h.2 u u.isLt).mem_iff.mpr hv⟩⟩, rfl⟩

include G h in
/-- The vertex cycles are indexed by the graph vertices. -/
theorem vertex_cycles (con : ConnectedInput n edges) (hn : 1 < n) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (rho rows))) = n := by
  let orig (x : Dart rows) : Fin n := ⟨x.val.1, h.1 ▸ (mem_darts.mp x.prop).1⟩
  let e : Quotient (Equiv.Perm.SameCycle.setoid (rho rows)) ≃ Fin n :=
    (Quotient.congrRight (r' := Setoid.ker orig) (fun x y =>
    (rho_sameCycle_iff (valid_of_legal G h) x y).trans
        (show (orig x).val = (orig y).val ↔ orig x = orig y from Fin.ext_iff.symm))).trans
    (Setoid.quotientKerEquivOfSurjective orig (origin_surjective h con hn))
  rw [Nat.card_congr e, Nat.card_fin]

end Map
end MultiGenus
