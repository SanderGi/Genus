/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.Solver
public import MultiGenus.Solver

/-! # HoG worker selection and its first-success rule

The scheduler takes completion events in the order the operating system delivers them.
A failed worker leaves the race. A materialized PAGE memory-limit event can start one
streaming replacement. A success commits the genus computed by that worker.
-/

@[expose] public section

namespace HoG

open MultiGenus MultiGenus.Rotations

/-- Detect connectivity by counting the edges of the rooted spanning tree. -/
def connected (n : Nat) (es : List Edge) : Bool :=
  decide (0 < n ∧ (Spanning.split n es).1.length + 1 = n)

theorem connected_iff {n es} (G : SimpleInput n es) :
    connected n es = true ↔ ConnectedInput n es := by
  simp only [connected, decide_eq_true_eq]
  constructor
  · rintro ⟨pos, len⟩
    exact (Spanning.connected_iff_tree_length G pos).2 len
  · intro con
    exact ⟨con.1, Spanning.tree_length G con⟩

/-- Deleting a bridge disconnects the input. HoG decomposes a materialized job
when this test succeeds, and runs the streaming search on the original graph. -/
def hasBridge (n : Nat) (es : List Edge) : Bool :=
  es.any fun e => !connected n (es.erase e)

theorem hasBridge_iff {n es} (G : SimpleInput n es) :
    hasBridge n es = true ↔ ∃ e ∈ es, ¬ ConnectedInput n (es.erase e) := by
  have sub (e : Edge) : SimpleInput n (es.erase e) :=
    ⟨fun d h => G.ordered d (List.mem_of_mem_erase h),
      fun d h => G.bounded d (List.mem_of_mem_erase h), G.nodup.erase e⟩
  simp [hasBridge, ← connected_iff (sub _)]

/-- A connected graph with one fewer edge than vertices has minimum genus zero. -/
theorem tree_minimum {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (tree : es.length + 1 = n) : minimumGenus n es = 0 := by
  obtain ⟨_, _, euler⟩ := (minimumGenus_isLeast G con).1
  omega

/-- A child algorithm in the native portfolio. -/
inductive Worker where
  | materialized | streaming | multiGenus
  deriving DecidableEq, Repr

/-- The mutually exclusive worker-selection options on the command line. -/
inductive Mode where
  | race | pageOnly | multiGenusOnly
  deriving DecidableEq, Repr

/-- Initial PAGE strategy and permitted memory-limit recovery. -/
inductive PageMode where
  | table | lowMemory | autoLowMemory
  deriving DecidableEq, Repr

/-- Select the supported workers requested by the user. -/
def launch (m : Mode) (p : PageMode) (supportsPage supportsMG : Bool) : List Worker :=
  let page := if p = .lowMemory then Worker.streaming else .materialized
  (if supportsPage && m != .multiGenusOnly then [page] else []) ++
    (if supportsMG && m != .pageOnly then [.multiGenus] else [])

/-- How a child process completed. Only a successful report may win the race. -/
inductive Outcome where
  | success | failure | cycleMemoryLimit
  deriving DecidableEq, Repr

/-- First successful active worker. A memory-limit event retires the table worker
and starts the streaming worker when automatic fallback is enabled. -/
def winner (p : PageMode) (active : List Worker) : List (Worker × Outcome) → Option Worker
  | [] => none
  | (w, o) :: events =>
    if w ∉ active then winner p active events
    else match o with
      | .success => some w
      | .failure => winner p (active.erase w) events
      | .cycleMemoryLimit =>
        let rest := active.erase w
        winner p (if p = .autoLowMemory ∧ w = .materialized then .streaming :: rest else rest)
          events

/-- Without resource failures, a nonempty launch returns the first child to complete. -/
theorem winner_first (p : PageMode) {ws : List Worker} {w : Worker} (mem : w ∈ ws)
    (later : List (Worker × Outcome)) : winner p ws ((w, .success) :: later) = some w := by
  simp [winner, mem]

/-- The resource-limit replacement can win even after the other child fails. -/
theorem winner_retry (later : List (Worker × Outcome)) :
    winner .autoLowMemory [.materialized, .multiGenus]
      ((.materialized, .cycleMemoryLimit) :: (.multiGenus, .failure) ::
        (.streaming, .success) :: later) = some .streaming := by rfl

/-- The execution layer accepts the block-aware materialized algorithm as its first worker. -/
def answer (table : Nat → List Edge → Option Nat) (n : Nat) (es : List Edge) :
    Worker → Option Nat
  | .materialized => table n es
  | .streaming => (Page.lowMemory n es).map Prod.fst
  | .multiGenus => (MultiGenus.solve n es).map Prod.fst

theorem answer_eq {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (table : Nat → List Edge → Option Nat) (ht : table n es = some (minimumGenus n es))
    (w : Worker) : answer table n es w = some (minimumGenus n es) := by
  cases w with
  | materialized => exact ht
  | streaming =>
    obtain ⟨g, fs, h, _, _, _, _, least⟩ := Page.lowMemory_correct G con
    simp [answer, h, least.unique (minimumGenus_isLeast G con)]
  | multiGenus =>
    obtain ⟨g, rs, h, _, _, least⟩ := MultiGenus.solve_correct G con
    simp [answer, h, least.unique (minimumGenus_isLeast G con)]

/-- Apply the tree shortcut or collect the first successful child from a supplied schedule.
An empty launch represents a graph outside the requested backends' limits. -/
def dispatch (table : Nat → List Edge → Option Nat) (p : PageMode) (active : List Worker)
    (events : List (Worker × Outcome)) (n : Nat) (es : List Edge) : Option Nat :=
  if active.isEmpty then none
  else if es.length + 1 = n then some 0
  else (winner p active events).bind (answer table n es)

/-- Exact result or exhaustion, for every order of child completion and failure. -/
theorem dispatch_eq {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (table : Nat → List Edge → Option Nat) (ht : table n es = some (minimumGenus n es))
    (p : PageMode) (ws : List Worker) (events : List (Worker × Outcome)) :
    dispatch table p ws events n es =
      if ws.isEmpty then none else if es.length + 1 = n ∨ (winner p ws events).isSome then
        some (minimumGenus n es) else none := by
  unfold dispatch
  by_cases h : es.length + 1 = n
  · simp [h, tree_minimum G con h]
  · cases winner p ws events <;> simp [h, answer_eq G con table ht]

end HoG
