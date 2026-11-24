/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
import HoG
import Lean.Util.CollectAxioms

/-! # HoG proof contracts, axiom audit and small executable controls -/

#lint in HoG

open MultiGenus HoG

example : ∀ {n es}, SimpleInput n es → ConnectedInput n es →
    ∀ (p : PageMode) (w : Worker) (ws : List Worker),
      ∃ g, HoG.solve p (w :: ws) n es = some g ∧ IsLeast {k | Realizes n es k} g :=
  fun G con => HoG.solve_correct G con

example : ∀ {n es p ws events g}, SimpleInput n es → ConnectedInput n es →
    HoG.run p ws events n es = some g → IsLeast {k | Realizes n es k} g :=
  HoG.run_correct

example {n es} (G : SimpleInput n es) (m : Mode) (p : PageMode) (g : Nat) :
    evaluate m p (n, es) = some g ↔
    ConnectedInput n es ∧ workers m p n es ≠ [] ∧ g = minimumGenus n es :=
  evaluate_iff G

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``HoG.solve_correct, ``HoG.run_eq, ``HoG.run_correct, ``HoG.materialized_eq,
      ``HoG.evaluate_iff, ``HoG.evaluateMultiCode_spec, ``HoG.evaluateGraph6_iff,
      ``HoG.Blocks.minimumGenus_vertexSum, ``HoG.minimum_split, ``HoG.tree_minimum,
      ``HoG.hasBridge_iff, ``HoG.Input.decodeMultiCode_succeeds_iff] do
    let extra := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "{decl} uses unexpected axioms {extra}"

example : evaluateGraph6 .race .table [64] = some (some 0) := by decide +kernel
example : evaluateGraph6 .race .table [65, 63] = some none := by decide +kernel
example : evaluateGraph6 .race .table [65, 64] = none := by decide +kernel

example : winner .table [.materialized, .multiGenus]
    [(.streaming, .success), (.materialized, .cycleMemoryLimit), (.multiGenus, .failure)]
    = none := by decide +kernel

example : winner .autoLowMemory [.materialized, .multiGenus]
    [(.materialized, .cycleMemoryLimit), (.materialized, .success), (.streaming, .success)]
    = some .streaming := by decide +kernel
