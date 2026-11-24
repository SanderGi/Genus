/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import Page
import Lean.Util.CollectAxioms

/-! # Audit PAGE's theorem contracts, axioms and executable certificate checker -/

#lint in Page

open Page MultiGenus MultiGenus.Rotations

example : ∀ n es, SimpleInput n es → ConnectedInput n es →
    ∃ g fs, materialized n es = some (g, fs) ∧
      Certificate.check n es fs = true ∧ Legal n es (Certificate.readRows n es fs) ∧
      Faces.faceCount (Certificate.readRows n es fs) = fs.length ∧
      2 + es.length = n + fs.length + 2 * g ∧ IsLeast {k | Realizes n es k} g :=
  fun _ _ => materialized_correct

example : ∀ n es, SimpleInput n es → ConnectedInput n es →
    ∃ g fs, lowMemory n es = some (g, fs) ∧
      Certificate.check n es fs = true ∧ Legal n es (Certificate.readRows n es fs) ∧
      Faces.faceCount (Certificate.readRows n es fs) = fs.length ∧
      2 + es.length = n + fs.length + 2 * g ∧ IsLeast {k | Realizes n es k} g :=
  fun _ _ => lowMemory_correct

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``materialized_correct, ``lowMemory_correct, ``agree,
      ``Certificate.realizes_iff_check, ``Seed.check_inputFaces,
      ``FaceBounds.lowerGenus_le_minimum, ``Walks.searchRoot_eq,
      ``Girth.girth_le_of_bridgeless, ``Girth.even_face_of_bipartite,
      ``CheckedDFS.compatible_of_check, ``Turns.check_iff_noShortTurns, ``Pruning.advance_one_genus,
      ``Pruning.Automorphism.replace_root] do
    let extra := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "{decl} uses unexpected axioms {extra}"

example : materialized 1 [] = some (0, [[]]) := by decide +kernel
example : lowMemory 1 [] = some (0, [[]]) := by decide +kernel
example : Certificate.check 2 [(0, 1)] [[(0, 1), (1, 0)]] = true := by decide +kernel
example : Certificate.check 2 [(0, 1)] [[(0, 1)], [(1, 0)]] = false := by decide +kernel

-- Both orientations of each edge are covered, but the two turns at the center
-- would give two singleton rotations there.
example : Certificate.check 3 [(0, 1), (0, 2)]
    [[(0, 1), (1, 0)], [(0, 2), (2, 0)]] = false := by decide +kernel
