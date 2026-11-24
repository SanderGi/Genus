/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Decompose
public import HoG.Portfolio

/-! # Eligibility of the portfolio's workers -/

@[expose] public section

namespace HoG

open MultiGenus.Rotations

/-- Highest degree in an adjacency list for the input. -/
def maxDegree (n : Nat) (es : List Edge) : Nat :=
  (List.range n).foldl (fun d v => max d (neighbors es v).length) 0

/-- Packed vertex, edge and degree limits for a materialized PAGE block. -/
def fitsBlock (n : Nat) (es : List Edge) : Bool :=
  n ≤ 65535 && es.length ≤ 65535 && maxDegree n es ≤ 255

/-- Check materialized limits on the blocks HoG will actually submit. -/
def fitsTable (n : Nat) (es : List Edge) : Bool :=
  if hasBridge n es then
    ((Decompose.build n es).fold fun k cs =>
      if cs.length == 1 || fitsBlock k cs then some 0 else none).isSome
  else fitsBlock n es

/-- Select workers for the standard 64-bit LONG build. `longBuild = false` selects
the smaller MultiGenus tables. The native operating system can also refuse an allocation. -/
def workers (m : Mode) (p : PageMode) (n : Nat) (es : List Edge)
    (longBuild : Bool := true) : List Worker :=
  let mg := if longBuild then n ≤ 128 && es.length ≤ 512 else n ≤ 64 && es.length ≤ 256
  let page := if m = .multiGenusOnly then false else if p = .lowMemory then
      0 < n && n ≤ 65535 && maxDegree n es < 65535 && 2 * es.length ≤ 4294967295
    else fitsTable n es
  launch m p page mg

end HoG
