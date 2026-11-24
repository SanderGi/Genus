/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Backtrack

/-! # Splitting a bounded insertion search between workers

The serial and split searches use the same insertion choices and genus bound.
At the split depth, workers take successive internal nodes in round-robin order.
A terminal node is checked before the C worker counter, so it can be seen by
every worker. Only existence and validity of a reported rotation matter here.
-/

@[expose] public section

namespace MultiGenus.Parallel

open Rotations Backtrack

/-- DFS order of the cut nodes, retaining a leaf reached before or at the cut.
A prefix already pruned above the cut contributes no tasks. -/
def frontier (n target : Nat) : Nat → Nat → Rows → List Edge → List Rows
  | _, _, r, [] => [r]
  | 0, _, r, _ :: _ => [r]
  | depth + 1, m, r, e :: es =>
    if target < genusOf n m r then [] else
      (insertEdge r e).flatMap (fun u => frontier n target depth (m + 1) u es)

/-- An internal cut node belongs to the worker indexed by its visit number modulo
the worker count. A terminal node at or above the cut bypasses worker selection. -/
def Reports (n target depth m : Nat) (r : Rows) (es : List Edge) {workers : Nat}
    (worker : Fin workers) (s : Rows) : Prop :=
  ∃ i : Fin (frontier n target depth m r es).length,
    (es.length ≤ depth ∨ i.val % workers = worker.val) ∧
    branch n target (m + (es.take depth).length) (frontier n target depth m r es)[i]
      (es.drop depth) = some s

/-- At every split depth, serial success is equivalent to success below some cut node. -/
theorem branch_iff_frontier (n t depth m : Nat) (r : Rows) (es : List Edge) :
    (branch n t m r es).isSome ↔
      ∃ u ∈ frontier n t depth m r es,
        (branch n t (m + (es.take depth).length) u (es.drop depth)).isSome := by
  induction depth generalizing es m r with
  | zero => cases es <;> simp [frontier]
  | succ d ih =>
    cases es with
    | nil => simp [frontier]
    | cons e es =>
      by_cases over : t < genusOf n m r
      · simp [branch, frontier, over]
      · simp only [branch, frontier, over, ite_false, List.findSome?_isSome_iff,
          List.mem_flatMap, List.take_succ_cons, List.length_cons, List.drop_succ_cons]
        constructor
        · rintro ⟨u, hu, ok⟩
          obtain ⟨v, hv, done⟩ := (ih (m + 1) u es).mp ok
          refine ⟨v, ⟨u, hu, hv⟩, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using done
        · rintro ⟨v, ⟨u, hu, hv⟩, done⟩
          apply Exists.intro u
          exact ⟨hu, (ih (m + 1) u es).mpr ⟨v, hv, by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using done⟩⟩

/-- Every successful subtree search has a worker, even when there are more workers than
tasks. Conversely, any worker report certifies feasibility in the serial search. -/
theorem branch_iff_worker (n t depth m : Nat) (r : Rows) (es : List Edge)
    {workers : Nat} (pos : 0 < workers) :
    (branch n t m r es).isSome ↔ ∃ (w : Fin workers) (s : Rows), Reports n t depth m r es w s := by
  rw [branch_iff_frontier n t depth m r es]
  constructor
  · rintro ⟨u, hu, found⟩
    obtain ⟨i, hi, eq⟩ := List.getElem_of_mem hu
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp found
    refine ⟨⟨i % workers, Nat.mod_lt _ pos⟩, s, ⟨i, hi⟩, Or.inr rfl, ?_⟩
    simpa [eq] using hs
  · rintro ⟨w, s, i, _, hs⟩
    exact ⟨_, List.getElem_mem i.isLt, Option.isSome_iff_exists.mpr ⟨s, hs⟩⟩

private theorem prefix_of_mem {n t d m : Nat} {r u : Rows} {es : List Edge}
    (h : u ∈ frontier n t d m r es) : Completes r (es.take d) u := by
  induction d generalizing es m r with
  | zero => cases es <;> simpa [frontier, Completes] using h
  | succ d ih =>
    cases es with
    | nil => simpa [frontier, Completes] using h
    | cons e es =>
      simp only [frontier] at h
      split at h
      · contradiction
      · obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp h
        exact ⟨v, hv, ih hu⟩

private theorem join {r u s : Rows} {xs ys : List Edge}
    (a : Completes r xs u) (b : Completes u ys s) : Completes r (xs ++ ys) s := by
  induction xs generalizing r with
  | nil => obtain rfl := a; exact b
  | cons e es ih =>
    obtain ⟨v, hv, done⟩ := a
    exact ⟨v, hv, ih done⟩

/-- Any worker can win the first-success race: its particular witness is a completion
of the original rotation with exactly the requested genus. -/
theorem reports_sound {n t d m workers : Nat} {r s : Rows} {es : List Edge} {w : Fin workers}
    (report : Reports n t d m r es w s) :
    Completes r es s ∧ genusOf n (m + es.length) s = t := by
  obtain ⟨i, _, found⟩ := report
  have pre := prefix_of_mem (n := n) (t := t) (d := d) (m := m) (r := r) (es := es)
    (List.getElem_mem i.isLt)
  obtain ⟨post, genus⟩ := branch_some found
  refine ⟨by simpa using join pre post, ?_⟩
  have len := congrArg List.length (List.take_append_drop d es)
  simp only [List.length_append] at len
  rwa [Nat.add_assoc, len] at genus

/-- On a legal connected spanning prefix the union of the worker subtrees realizes
exactly the serial attainable genera, independently of scheduling and split depth. -/
theorem workers_iff_attainable {n t workers : Nat} (depth : Nat) {pre es : List Edge} {r : Rows}
    (pos : 0 < workers) (G : SimpleInput n (pre ++ es)) (con : ConnectedInput n pre)
    (hr : Legal n pre r) :
    (∃ (w : Fin workers) (s : Rows), Reports n t depth pre.length r es w s) ↔
      ∃ s, Completes r es s ∧ genusOf n (pre ++ es).length s = t := by
  constructor
  · rintro ⟨w, s, found⟩
    obtain ⟨hs, hg⟩ := reports_sound found
    exact ⟨s, hs, by simpa using hg⟩
  · rintro ⟨s, hs, hg⟩
    exact (branch_iff_worker _ _ depth _ _ _ pos).mp (branch_finds G con hr hs hg)

end MultiGenus.Parallel
