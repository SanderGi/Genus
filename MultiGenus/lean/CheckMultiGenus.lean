/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import MultiGenus
import Lean.Util.CollectAxioms

/-! # Declaration lint, theorem contract, axiom audit and small executable examples -/

#lint in MultiGenus

open MultiGenus MultiGenus.Rotations

example : ∀ n edges, SimpleInput n edges → ConnectedInput n edges →
    ∃ g r, solve n edges = some (g, r) ∧ Legal n edges r ∧
      2 + edges.length = n + Faces.faceCount r + 2 * g ∧ IsLeast {k | Realizes n edges k} g :=
  fun _ _ => solve_correct

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``solve_correct, ``minimumGenus_isLeast, ``exactGenus_iff,
      ``LowerBound.initial_le, ``euler_genus, ``Extension.faceCount_insertEdge,
      ``Reduction.triangle_minimum_iff, ``Pruning.no_completion_within_budget,
      ``Reflection.realizes_iff_agreesWithSeed, ``Representation.attains_iff_realizes,
      ``MultiCode.decodeOne_simple, ``Parallel.workers_iff_attainable] do
    let extra := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "{decl} uses unexpected axioms {extra}"

example : solve 1 [] = some (0, [[]]) := by decide +kernel
example : solve 2 [(0, 1)] = some (0, [[1], [0]]) := by decide +kernel
example : exactGenus 2 [(0, 1)] 1 = none := by decide +kernel
example : ¬ Legal 2 [(0, 1)] [[1], []] := by
  intro h
  have missing := h.2 1 (by decide)
  contradiction
