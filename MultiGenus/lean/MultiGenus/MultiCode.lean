/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Graph
import Mathlib.Data.List.Nodup

/-! # Single-byte multicode graph records

The first byte gives the order, from 1 to 255. For each vertex except the
last, its larger neighbors are given as one-based bytes terminated by zero.
The row interface uses zero-based neighbor indices and omits the last row.
-/

@[expose] public section

namespace MultiGenus.MultiCode

open Rotations

/-- Well-formed upper-triangular rows for an order-`n` graph, beginning at origin `u`. -/
def ValidRows (n u : Nat) : List (List Nat) → Prop
  | [] => True
  | vs :: rs => (∀ v ∈ vs, u < v ∧ v < n) ∧ vs.Nodup ∧ ValidRows n (u + 1) rs

instance validRowsDecidable (n : Nat) (u : Nat) (rs : List (List Nat)) :
    Decidable (ValidRows n u rs) :=
  match rs with
  | [] => isTrue trivial
  | vs :: rs =>
    letI := validRowsDecidable n (u + 1) rs
    inferInstanceAs (Decidable ((∀ v ∈ vs, u < v ∧ v < n) ∧ vs.Nodup ∧ ValidRows n (u + 1) rs))

/-- List edges by increasing origin and then increasing neighbor. -/
def canonicalEdges (u : Nat) : List (List Nat) → List Edge
  | [] => []
  | vs :: rs => vs.mergeSort.map (u, ·) ++ canonicalEdges (u + 1) rs

private theorem origin_le {rs : List (List Nat)} {e : Edge} {u : Nat}
    (he : e ∈ canonicalEdges u rs) : u ≤ e.1 := by
  induction rs generalizing u with
  | nil => simp [canonicalEdges] at he
  | cons xs rs ih =>
    rcases List.mem_append.mp he with h | h
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih h)

/-- Canonical edges from valid rows give a simple undirected input. -/
theorem simpleInput_of_validRows {n u : Nat} {rs : List (List Nat)} (h : ValidRows n u rs) :
    SimpleInput n (canonicalEdges u rs) := by
  induction rs generalizing u with
  | nil => exact ⟨by simp [canonicalEdges], by simp [canonicalEdges], by simp [canonicalEdges]⟩
  | cons xs rs ih =>
    obtain ⟨bounds, nd, legal⟩ := h
    have tail := ih legal
    have left {e : Edge} (he : e ∈ xs.mergeSort.map (u, ·)) : e.1 < e.2 ∧ e.2 < n := by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      exact bounds v (List.mem_mergeSort.mp hv)
    constructor
    · intro e he
      exact (List.mem_append.mp he).elim (fun h => (left h).1) (tail.ordered e)
    · intro e he
      exact (List.mem_append.mp he).elim (fun h => (left h).2) (tail.bounded e)
    · refine List.nodup_append.mpr ⟨List.Nodup.map (fun _ _ e => congrArg Prod.snd e)
          ((List.mergeSort_perm xs _).nodup_iff.mpr nd), tail.nodup, ?_⟩
      intro e he f hf eq
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
      subst f
      have := origin_le hf
      omega

/-- Serialized row data, including one terminator per explicit row. -/
def body (rs : List (List Nat)) : List Nat := rs.flatMap fun vs => vs.map Nat.succ ++ [0]

/-- Read one zero-terminated row and convert its neighbors to zero-based indices. -/
def readRow (bytes : List Nat) : Option (List Nat × List Nat) :=
  match bytes.dropWhile (· != 0) with
  | 0 :: rest => some ((bytes.takeWhile (· != 0)).map Nat.pred, rest)
  | _ => none

/-- Consume exactly the requested number of rows and leave the suffix untouched. -/
def readRows : Nat → List Nat → Option (List (List Nat) × List Nat)
  | 0, bytes => some ([], bytes)
  | k + 1, bytes => (readRow bytes).bind fun a =>
    (readRows k a.2).map fun b => (a.1 :: b.1, b.2)

/-- Decode a single headerless record; allow any ordering within a neighbor row. -/
def decodeOne : List Nat → Except String (Nat × List Edge × List Nat)
  | [] => .error "missing multicode order"
  | n :: bytes =>
    if n = 0 ∨ 255 < n then .error "multicode order must be in 1..255"
    else match readRows (n - 1) bytes with
      | none => .error "missing multicode row terminator"
      | some (rs, rest) =>
        if ValidRows n 0 rs then .ok (n, canonicalEdges 0 rs, rest)
        else .error "repeated neighbor or neighbor outside the strict upper triangle"

/-- Encode zero-based neighbor rows in their supplied order. The implicit last vertex
has no larger neighbors, so the graph order is one greater than the row count. -/
def encodeRows (rs : List (List Nat)) : Except String (List Nat) :=
  let n := rs.length + 1
  if 255 < n then .error "multicode order exceeds 255"
  else if ValidRows n 0 rs then .ok (n :: body rs)
  else .error "repeated neighbor or neighbor outside the strict upper triangle"

private theorem readRow_spec (bytes vs rest : List Nat) :
    readRow bytes = some (vs, rest) ↔ bytes = vs.map Nat.succ ++ 0 :: rest := by
  induction bytes generalizing vs with
  | nil => cases vs <;> simp [readRow]
  | cons x bytes ih =>
    cases x with
    | zero => cases vs <;> simp [readRow]
    | succ x =>
      have cons : readRow ((x + 1) :: bytes) =
          (readRow bytes).map (fun (ws, r) => (x :: ws, r)) := by
        simp [readRow]
        split <;> rfl
      rw [cons, Option.map_eq_some_iff]
      cases vs <;> simp [ih, and_comm]

private theorem readRows_spec (k : Nat) (bytes : List Nat) (rs : List (List Nat))
    (rest : List Nat) :
    readRows k bytes = some (rs, rest) ↔ rs.length = k ∧ bytes = body rs ++ rest := by
  induction k generalizing bytes rs with
  | zero => cases rs <;> simp [readRows, body, eq_comm]
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨⟨vs, t⟩, first, after⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨tail, s⟩, parsed, eq⟩ := Option.map_eq_some_iff.mp after
      cases eq
      obtain ⟨len, suffix⟩ := (ih _ _).mp parsed
      refine ⟨by simp [len], ?_⟩
      change t = body tail ++ s at suffix
      rw [(readRow_spec _ _ _).mp first, suffix]
      simp [body, List.append_assoc]
    · rintro ⟨len, rfl⟩
      cases rs with
      | nil => simp at len
      | cons vs tail =>
        have ht : tail.length = k := by simpa using len
        apply Option.bind_eq_some_iff.mpr
        refine ⟨(vs, body tail ++ rest), (readRow_spec _ _ _).mpr ?_, ?_⟩
        · simp [body, List.append_assoc]
        · exact Option.map_eq_some_iff.mpr ⟨(tail, rest), (ih _ _).mpr ⟨ht, rfl⟩, rfl⟩

/-- A successful decoding identifies the precise consumed record and its canonical edges. -/
theorem decodeOne_spec {bytes rest : List Nat} {n : Nat} {edges : List Edge} :
    decodeOne bytes = .ok (n, edges, rest) ↔
      1 ≤ n ∧ n ≤ 255 ∧ ∃ rs, rs.length = n - 1 ∧ ValidRows n 0 rs ∧
        bytes = n :: (body rs ++ rest) ∧ edges = canonicalEdges 0 rs := by
  cases bytes with
  | nil => simp [decodeOne]
  | cons m bytes =>
    constructor
    · intro h
      rw [decodeOne] at h
      split at h
      · contradiction
      · rename_i size
        split at h
        · contradiction
        · rename_i rs r parsed
          split at h
          · rename_i good
            cases h
            obtain ⟨len, framing⟩ := (readRows_spec _ _ _ _).mp parsed
            exact ⟨by omega, by omega, rs, len, good, congrArg (_ :: ·) framing, rfl⟩
          · contradiction
    · rintro ⟨lo, hi, rs, len, good, eq, rfl⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj eq
      have parsed := (readRows_spec (m - 1) (body rs ++ rest) rs rest).mpr ⟨len, rfl⟩
      simp [decodeOne, Nat.ne_of_gt lo, Nat.not_lt.mpr hi, parsed, good]

/-- A successful record always produces a simple graph in the indicated vertex range. -/
theorem decodeOne_simple {bytes rest : List Nat} {n : Nat} {edges : List Edge}
    (h : decodeOne bytes = .ok (n, edges, rest)) : SimpleInput n edges := by
  obtain ⟨_, _, _, _, good, _, rfl⟩ := decodeOne_spec.mp h
  exact simpleInput_of_validRows good

/-- A zero in the emitted body always marks the end of one explicit row. -/
theorem body_count_zero (rs : List (List Nat)) : (body rs).count 0 = rs.length := by
  induction rs with
  | nil => rfl
  | cons vs rs ih =>
    have h : 0 ∉ vs.map Nat.succ := by simp
    change ((vs.map Nat.succ ++ [0]) ++ body rs).count 0 = rs.length + 1
    simp [List.count_eq_zero_of_not_mem h, ih]

/-- Exactly `n - 1` zero bytes are consumed, regardless of the contents of the suffix. -/
theorem decodeOne_boundary {bytes rest : List Nat} {n : Nat} {edges : List Edge}
    (h : decodeOne bytes = .ok (n, edges, rest)) :
    ∃ payload, bytes = n :: (payload ++ rest) ∧ payload.count 0 = n - 1 := by
  obtain ⟨_, _, rs, len, _, eq, _⟩ := decodeOne_spec.mp h
  exact ⟨body rs, eq, (body_count_zero rs).trans len⟩

/-- Every valid collection of rows of single-byte order can be written. -/
theorem encodeRows_ok {rs : List (List Nat)} (size : rs.length + 1 ≤ 255)
    (valid : ValidRows (rs.length + 1) 0 rs) :
    encodeRows rs = .ok ((rs.length + 1) :: body rs) := by
  simp [encodeRows, Nat.not_lt.mpr size, valid]

/-- Writing and then reading a valid record preserves the graph and any subsequent bytes. -/
theorem decodeOne_encodeRows {rs : List (List Nat)} {encoded : List Nat}
    (wrote : encodeRows rs = .ok encoded) (suffix : List Nat) :
    decodeOne (encoded ++ suffix) = .ok (rs.length + 1, canonicalEdges 0 rs, suffix) := by
  simp only [encodeRows] at wrote
  split at wrote
  · contradiction
  · rename_i size
    split at wrote
    · rename_i good
      cases wrote
      exact decodeOne_spec.mpr ⟨by omega, by omega, rs, by omega, good, rfl, rfl⟩
    · contradiction

end MultiGenus.MultiCode
