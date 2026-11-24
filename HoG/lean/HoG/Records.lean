/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Input
public import HoG.Launch
public import HoG.Solver
import Batteries.Data.List.Lemmas

/-! # Per-record validation and genus results for House of Graphs streams -/

@[expose] public section

namespace HoG

open MultiGenus MultiGenus.Rotations

/-- Evaluate one decoded record in the standard LONG build. A disconnected record or an
empty launch has no genus result. -/
def evaluate (m : Mode) (p : PageMode) (graph : Input.Graph) : Option Nat :=
  if connected graph.1 graph.2 then solve p (workers m p graph.1 graph.2) graph.1 graph.2
  else none

/-- Exactly the supported, connected records report a value, and that value is the minimum. -/
theorem evaluate_iff {n es} (G : SimpleInput n es) {m p g} :
    evaluate m p (n, es) = some g ↔
      ConnectedInput n es ∧ workers m p n es ≠ [] ∧ g = minimumGenus n es := by
  by_cases con : ConnectedInput n es
  · have yes := (connected_iff G).mpr con
    cases hw : workers m p n es with
    | nil =>
      have noWorker : solve p [] n es = none := rfl
      simp [evaluate, yes, hw, noWorker]
    | cons w ws =>
      obtain ⟨k, val, least⟩ := solve_correct G con p w ws
      have eq := least.unique (minimumGenus_isLeast G con)
      have hit : evaluate m p (n, es) = some (minimumGenus n es) := by
        simp [evaluate, yes, hw, val, eq]
      rw [hit]
      exact ⟨fun h => ⟨con, List.cons_ne_nil _ _, (Option.some.inj h).symm⟩,
        fun h => congrArg some h.2.2.symm⟩
  · have no : connected n es = false := Bool.eq_false_iff.mpr fun h => con ((connected_iff G).mp h)
    simp [evaluate, no, con]

/-- Failure of an individual valid record has precisely the two input-level causes:
disconnection or no eligible worker in the selected mode. -/
theorem evaluate_none_iff {n es} (G : SimpleInput n es) {m p} :
    evaluate m p (n, es) = none ↔ ¬ ConnectedInput n es ∨ workers m p n es = [] := by
  constructor
  · intro fail
    by_contra! h
    have yes := (evaluate_iff G).mpr ⟨h.1, h.2, rfl⟩
    simp [fail] at yes
  · intro h
    cases eq : evaluate m p (n, es) with
    | none => rfl
    | some g =>
      have proved := (evaluate_iff G).mp eq
      exact (h.elim (fun neg => neg proved.1) (fun empty => proved.2.1 empty)).elim

/-- Evaluate every decoded record, keeping a missing result in place so later records run.
An outer `none` means that decoding the input failed. -/
def evaluateStream {α : Type*} (decode : α → Option (List Input.Graph)) (m : Mode)
    (p : PageMode) (input : α) : Option (List (Option Nat)) :=
  (decode input).map (List.map (evaluate m p))

/-- Pair decoded graphs with their result slots in input order, including failure slots. -/
theorem evaluateStream_spec {α : Type*} {decode : α → Option (List Input.Graph)} {input gs}
    (decoded : decode input = some gs) (simple : ∀ graph ∈ gs, SimpleInput graph.1 graph.2)
    (m : Mode) (p : PageMode) :
    ∃ results, evaluateStream decode m p input = some results ∧
      List.Forall₂ (fun graph (out : Option Nat) => ∀ g, out = some g ↔
        ConnectedInput graph.1 graph.2 ∧ workers m p graph.1 graph.2 ≠ [] ∧
        g = minimumGenus graph.1 graph.2) gs results := by
  refine ⟨gs.map (evaluate m p), by simp [evaluateStream, decoded], ?_⟩
  clear decoded
  induction gs with
  | nil => exact .nil
  | cons graph gs ih =>
    exact .cons (fun _ => evaluate_iff (simple graph (.head _)))
      (ih (fun x hx => simple x (.tail _ hx)))

/-- Evaluate one graph6 record after the caller has identified its line boundaries. -/
def evaluateGraph6 (m : Mode) (p : PageMode) (record : List Nat) : Option (Option Nat) :=
  (Input.decodeGraph6 record).map (evaluate m p)

/-- A graph6 genus result certifies both its decoded input and its exact optimum. -/
theorem evaluateGraph6_iff {m p record g} : evaluateGraph6 m p record = some (some g) ↔
    ∃ graph, Input.decodeGraph6 record = some graph ∧ ConnectedInput graph.1 graph.2 ∧
      workers m p graph.1 graph.2 ≠ [] ∧ g = minimumGenus graph.1 graph.2 := by
  rw [evaluateGraph6, Option.map_eq_some_iff]
  constructor <;> rintro ⟨⟨n,es⟩, read, h⟩
  · exact ⟨_, read, (evaluate_iff (Input.decodeGraph6_simple read)).mp h⟩
  · exact ⟨_, read, (evaluate_iff (Input.decodeGraph6_simple read)).mpr h⟩

/-- Strip graph6 stream framing, retaining each record's exact ASCII payload. Native
whitespace includes the six ASCII space characters, including form feed and vertical tab. -/
def graph6Payloads (bytes : ByteArray) : List (List Nat) :=
  let space (b : Nat) := b == 32 || (9 ≤ b && b ≤ 13)
  let header := ">>graph6<<".toUTF8.data.toList.map UInt8.toNat
  let lines := List.splitOn 10 (bytes.data.toList.map UInt8.toNat)
  lines.filterMap fun raw =>
    let line := ((raw.dropWhile space).reverse.dropWhile space).reverse
    if line.isEmpty || line == header then none else
      some (if header.isPrefixOf line then line.drop header.length else line)

/-- Decode all records before evaluating any. An empty stream or a single malformed
payload rejects the whole graph6 input. -/
def decodeGraph6Stream (bytes : ByteArray) : Option (List Input.Graph) :=
  let records := graph6Payloads bytes
  if records.isEmpty then none else records.mapM Input.decodeGraph6

/-- Graph6 decoding succeeds precisely for a nonempty sequence of valid record payloads,
in their original order. -/
theorem decodeGraph6Stream_spec {bytes gs} : decodeGraph6Stream bytes = some gs ↔
    graph6Payloads bytes ≠ [] ∧
      List.Forall₂ (fun payload graph => Input.decodeGraph6 payload = some graph)
        (graph6Payloads bytes) gs := by
  by_cases empty : graph6Payloads bytes = []
  · simp [decodeGraph6Stream, empty]
  · simp only [decodeGraph6Stream, List.isEmpty_iff, ne_eq, empty, ↓reduceIte, not_false_eq_true,
      true_and, List.mapM_eq_some_iff_forall₂]

/-- Each record in a successfully decoded graph6 stream is a simple graph. -/
theorem decodeGraph6Stream_simple {bytes gs} (decoded : decodeGraph6Stream bytes = some gs)
    (g : Input.Graph) (hg : g ∈ gs) : SimpleInput g.1 g.2 := by
  have rel := (decodeGraph6Stream_spec.mp decoded).2
  clear decoded
  generalize graph6Payloads bytes = lines at rel
  induction rel with
  | nil => contradiction
  | cons hd _ ih =>
    rcases List.mem_cons.mp hg with rfl | mem
    · exact Input.decodeGraph6_simple hd
    · exact ih mem

/-- Read and evaluate a raw graph6 stream. -/
def evaluateGraph6Stream := evaluateStream decodeGraph6Stream

/-- In a successfully framed graph6 stream, every result is the minimum of its supported
connected record and each failed record retains its own result slot. -/
theorem evaluateGraph6Stream_spec {bytes gs} (decoded : decodeGraph6Stream bytes = some gs)
    (m : Mode) (p : PageMode) :
    ∃ results, evaluateGraph6Stream m p bytes = some results ∧
      List.Forall₂ (fun graph (out : Option Nat) => ∀ g, out = some g ↔
        ConnectedInput graph.1 graph.2 ∧ workers m p graph.1 graph.2 ≠ [] ∧
        g = minimumGenus graph.1 graph.2) gs results :=
  evaluateStream_spec decoded (decodeGraph6Stream_simple decoded) m p

/-- Decode an entire mixed-width multicode byte stream, then evaluate its records separately. -/
def evaluateMultiCode := evaluateStream Input.decodeMultiCode

/-- Every multicode result slot corresponds to its decoded record, including an unsupported
or disconnected record between two successful ones. -/
theorem evaluateMultiCode_spec {bytes gs} (decoded : Input.decodeMultiCode bytes = some gs)
    (m : Mode) (p : PageMode) :
    ∃ results, evaluateMultiCode m p bytes = some results ∧
      List.Forall₂ (fun graph (out : Option Nat) => ∀ g, out = some g ↔
        ConnectedInput graph.1 graph.2 ∧ workers m p graph.1 graph.2 ≠ [] ∧
        g = minimumGenus graph.1 graph.2) gs results :=
  evaluateStream_spec decoded (Input.decodeMultiCode_simple decoded) m p

end HoG
