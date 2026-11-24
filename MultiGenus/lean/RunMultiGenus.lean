/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import MultiGenus.MultiCode
import MultiGenus.Solver
import Lean.Data.Json.FromToJson.Basic

/-! # Run the verified solver on a single-byte multicode stream -/

open MultiGenus Lean

private def runFile (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let header := ">>multi_code<<".toUTF8.data.toList.map UInt8.toNat
  let mut rest := bytes.data.toList.map UInt8.toNat
  while !rest.isEmpty do
    if header.isPrefixOf rest then
      rest := rest.drop header.length
      if rest.isEmpty then break
    let (n, edges, tail) ← IO.ofExcept <|
      (MultiCode.decodeOne rest).mapError (fun msg => s!"{path}: {msg}")
    rest := tail
    unless (Spanning.split n edges).1.length + 1 == n do
      throw <| IO.userError s!"Disconnected graph in {path}"
    let some (g, r) := solve n edges
      | throw <| IO.userError s!"No genus witness returned for {path}"
    IO.println <| (Json.mkObj [("genus", toJson g), ("rotation", toJson r)]).compress

/-- Print one JSON record per graph, with zero-based vertex labels. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run lean/RunMultiGenus.lean FILE.mc ..."
    return 2
  for path in args do runFile path
  return 0
