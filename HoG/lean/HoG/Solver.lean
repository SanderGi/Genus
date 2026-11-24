/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Portfolio
public import HoG.Decompose
public import HoG.Blocks

/-! # The block-aware House of Graphs solver -/

@[expose] public section

namespace HoG

open MultiGenus MultiGenus.Rotations

/-- Materialized PAGE on one block. In particular a bridge block contributes zero. -/
def blockWorker (n : Nat) (es : List Edge) : Option Nat :=
  if es.length + 1 = n then some 0 else (Page.materialized n es).map Prod.fst

theorem blockWorker_eq {n es} (G : SimpleInput n es) (con : ConnectedInput n es) :
    blockWorker n es = some (minimumGenus n es) := by
  obtain ⟨g, fs, h, _, _, _, _, least⟩ := Page.materialized_correct G con
  by_cases tree : es.length + 1 = n
  · simp [blockWorker, tree, tree_minimum G con tree]
  · simp [blockWorker, tree, h, least.unique (minimumGenus_isLeast G con)]

/-- Use the whole graph when it has no bridge. Otherwise add the materialized
workers' results over the certified decomposition. -/
def materialized (n : Nat) (es : List Edge) : Option Nat :=
  if hasBridge n es then (Decompose.build n es).fold blockWorker else blockWorker n es

theorem minimum_split {n es} (s : Decompose.Split n es) (G : SimpleInput n es)
    (con : ConnectedInput n es) :
    minimumGenus n es = minimumGenus s.nL s.esL + minimumGenus s.nR s.esR := by
  obtain ⟨e, adj⟩ := s.relabel
  have sumG := VertexSum.simple s.simpleL s.simpleR s.connectedL.1
  have sumC := VertexSum.connected s.connectedL s.connectedR
  rw [← VertexSum.minimumGenus_relabel_fin sumG G sumC con e adj]
  exact Blocks.minimumGenus_vertexSum s.simpleL s.simpleR s.connectedL s.connectedR
    s.nontrivialL s.nontrivialR

theorem materialized_eq {n es} (G : SimpleInput n es) (con : ConnectedInput n es) :
    materialized n es = some (minimumGenus n es) := by
  unfold materialized
  split
  · exact (Decompose.build n es).fold_eq_some minimumGenus blockWorker
      blockWorker_eq minimum_split G con
  · exact blockWorker_eq G con

/-- HoG with arbitrary completion order, enabled workers and resource outcomes. -/
def run := dispatch materialized

/-- Precisely when the native control flow can report a genus. -/
def reports (p : PageMode) (ws : List Worker) (events : List (Worker × Outcome))
    (n : Nat) (es : List Edge) : Bool :=
  !ws.isEmpty && (es.length + 1 == n || (winner p ws events).isSome)

/-- Every reported result is the minimum; an exhausted schedule produces no result. -/
theorem run_eq {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (p : PageMode) (ws : List Worker) (events : List (Worker × Outcome)) :
    run p ws events n es = if reports p ws events n es then some (minimumGenus n es) else none := by
  rw [run, dispatch_eq G con _ (materialized_eq G con)]
  cases h : ws.isEmpty <;> simp [reports, h]

/-- Every successful HoG result minimizes genus over all rotations and is attained. -/
theorem run_correct {n es p ws events g} (G : SimpleInput n es) (con : ConnectedInput n es)
    (result : run p ws events n es = some g) : IsLeast {k | Realizes n es k} g := by
  rw [run_eq G con] at result
  split at result
  · cases result
    exact minimumGenus_isLeast G con
  · contradiction

/-- A normal completion schedule, given the selected workers in order of completion. -/
def solve (p : PageMode) (ws : List Worker) (n : Nat) (es : List Edge) : Option Nat :=
  run p ws (ws.map (·, .success)) n es

/-- Every nonempty worker choice yields a witnessed minimum on connected simple inputs. -/
theorem solve_correct {n es} (G : SimpleInput n es) (con : ConnectedInput n es)
    (p : PageMode) (w : Worker) (ws : List Worker) :
    ∃ g, solve p (w :: ws) n es = some g ∧ IsLeast {k | Realizes n es k} g := by
  refine ⟨_, ?_, minimumGenus_isLeast G con⟩
  rw [solve, run_eq G con]
  simp [reports, winner]

end HoG
