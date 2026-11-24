/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import HoG.Records

/-! # Read House of Graphs records from standard input and run the verified solver -/

open HoG

private def usage :=
  "Usage: lean --run lean/RunHoG.lean [--multicode|--graph6] " ++
    "[--page-only|--multi_genus-only] [--low-mem|--auto-low-mem] < graphs"

/-- Print one minimum genus per supported connected record. -/
def main (args : List String) : IO UInt32 := do
  let multi := args.contains "--multi_genus-only"
  let page := args.contains "--page-only"
  let low := args.contains "--low-mem"
  let auto := args.contains "--auto-low-mem"
  let binary := args.contains "--multicode"
  let flags := ["--graph6", "--multicode", "--page-only", "--multi_genus-only",
    "--low-mem", "--auto-low-mem"]
  if !(args.all (· ∈ flags)) || (multi && (page || low || auto)) || (low && auto) ||
      (binary && args.contains "--graph6") then
    IO.eprintln usage
    return 2
  let m : Mode := if multi then .multiGenusOnly else if page then .pageOnly else .race
  let p : PageMode := if low then .lowMemory else if auto then .autoLowMemory else .table
  let bytes ← (← IO.getStdin).readBinToEnd
  let some graphs := (if binary then Input.decodeMultiCode (bytes.data.toList.map UInt8.toNat)
      else decodeGraph6Stream bytes) | do
    IO.eprintln "Empty or malformed graph stream"
    return 1
  let mut errors := false
  for (graph, i) in graphs.zipIdx do
    match evaluate m p graph with
    | some g => IO.println s!"Graph {i+1} has genus {g}"
    | none =>
      IO.eprintln s!"Graph {i+1} is disconnected or exceeds the selected workers' limits"
      errors := true
  return if errors then 1 else 0
