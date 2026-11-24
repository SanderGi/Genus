/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import Page.Solver
import MultiGenus.Spanning
import Lean.Data.Json.FromToJson.Basic

/-! # Run either verified PAGE search on adjacency-list files -/

open MultiGenus MultiGenus.Rotations Lean

private def numbers (line : String) : Except String (List Nat) :=
  (line.splitToList Char.isWhitespace).filterMapM fun token =>
    if token.isEmpty then pure none
    else match token.toNat? with
      | some x => pure (some x)
      | none => throw s!"Invalid vertex or graph size '{token}'"

private def decode (text : String) : Except String (Nat × List Edge × Nat) := do
  let header :: rest := text.splitOn "\n" | throw "Missing header"
  let [n, m] ← numbers header | throw "Expected vertex and edge counts"
  if n == 0 then throw "Expected a nonempty graph"
  let mut rows := (← (rest.take n).mapM numbers).map (·.filter (· != 65535))
  if n == 1 && m == 0 && rows.isEmpty then rows := [[]]
  unless rows.length == n && (rest.drop n).all (·.trimAscii.isEmpty) do
    throw "Wrong number of adjacency rows"
  let start := rows.flatten.min?.getD 0
  unless rows.all (fun r => r.all (· < start + n) && r.Nodup) do
    throw "Duplicate or out-of-range neighbor"
  rows := rows.map fun r => r.map (· - start)
  let es := (rows.zipIdx).flatMap fun (r, u) => (r.filter (u < ·)).map (u, ·)
  unless es.length == m && (rows.zipIdx).all (fun (r, u) => r.isPerm (neighbors es u)) do
    throw "Edge count or reverse adjacency does not match"
  unless (Spanning.split n es).1.length + 1 == n do throw "Expected a connected graph"
  return (n, es, start)

private def runGraph (stream : Bool) (file : System.FilePath) : IO Unit := do
  let (n, es, start) ← IO.ofExcept <| decode (← IO.FS.readFile file)
  let some (g, fs) := Page.solve stream n es | throw <| IO.userError "No embedding found"
  let faces := fs.map fun f => f.map (·.1 + start) ++ [(f.head?.map (·.1 + start)).getD start]
  IO.println <| (Json.mkObj [("genus", toJson g), ("faces", toJson faces)]).compress

/-- Emit one JSON face certificate per input using the selected traversal. -/
def main (args : List String) : IO UInt32 := do
  let mode :: files := args | throw <| IO.userError "Expected materialized or low-memory and a file"
  unless (mode == "materialized" || mode == "low-memory") && !files.isEmpty do
    throw <| IO.userError "Usage: lean --run lean/RunPage.lean {materialized|low-memory} FILE ..."
  for file in files do runGraph (mode == "low-memory") file
  return 0
