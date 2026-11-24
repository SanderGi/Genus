/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Canonical
public import MultiGenus.Genus
import Init.Data.List.MinMaxOn

/-! # A witnessed minimum over orientable rotation systems -/

@[expose] public section

namespace MultiGenus

open Rotations Faces

/-- A rotation realizing the greatest number of face orbits. -/
def bestRotation (n : Nat) (edges : List Edge) : Rows :=
  (Canonical.enumerate n edges).maxOn faceCount (Canonical.enumerate_ne_nil n edges)

/-- Executable reference result for a connected simple input. -/
def minimumGenus (n : Nat) (edges : List Edge) : Nat :=
  genusOf n edges.length (bestRotation n edges)

/-- The minimizing rotation returned by the search has the original graph's incidences. -/
theorem bestRotation_legal (n : Nat) (edges : List Edge) : Legal n edges (bestRotation n edges) :=
  Canonical.legal_of_mem List.maxOn_mem

/-- The output face count bounds that of every cyclic ordering at every vertex. -/
theorem faceCount_le_best {n : Nat} {edges : List Edge} {r : Rows}
    (G : SimpleInput n edges) (hr : Legal n edges r) :
    faceCount r ≤ faceCount (bestRotation n edges) := by
  obtain ⟨s, hs, eq⟩ := Canonical.exists_same_faces G hr
  rw [← eq]
  exact List.le_apply_maxOn_of_mem hs

/-- Correctness of orientable minimum genus search for every connected nonempty simple graph.
An embedding attaining the result exists, and every rotation satisfying Euler's formula has
at least that genus. -/
theorem minimumGenus_isLeast {n : Nat} {edges : List Edge} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) : IsLeast {g | Realizes n edges g} (minimumGenus n edges) := by
  refine ⟨⟨_, bestRotation_legal n edges, euler_genus G con (bestRotation_legal n edges)⟩, ?_⟩
  rintro g ⟨r, hr, hg⟩
  have best := euler_genus G con (bestRotation_legal n edges)
  have bound := faceCount_le_best G hr
  unfold minimumGenus
  omega

end MultiGenus
