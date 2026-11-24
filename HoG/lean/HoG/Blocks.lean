/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.BlockCoordinates
public import HoG.MaxFaces

/-! # Additivity of orientable genus at an articulation vertex

The dart coordinates separate the root of each block from its other vertices.
Maximizing over every cyclic order at the common root costs one face. The graph
also loses one vertex, so Euler's formula adds the two component genera.
-/

public section

namespace HoG.Blocks

open MultiGenus MultiGenus.Rotations BlockCoordinates

/-- The genus obtained by identifying the two roots is the sum of the component minima.
A block may consist of a single bridge edge, with one dart at its root. -/
theorem minimumGenus_vertexSum {nL nR esL esR}
    (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (cL : ConnectedInput nL esL) (cR : ConnectedInput nR esR) (hL : 1 < nL) (hR : 1 < nR) :
    minimumGenus (VertexSum.vertices nL nR) (VertexSum.edges nL esL esR) =
      minimumGenus nL esL + minimumGenus nR esR := by
  let _ := root_nonempty GL cL hL
  let _ := root_nonempty GR cR hR
  have vertices := VertexSum.vertices_eq (nL := nL) cR.1
  have hn : 1 < VertexSum.vertices nL nR := by omega
  obtain ⟨l, hl, el⟩ := MaxFaces.of_graph GL cL (VertexSum.legal nL esL) hL
  obtain ⟨r, hr, er⟩ := MaxFaces.of_graph GR cR (VertexSum.legal nR esR) hR
  obtain ⟨k, hk, ek⟩ := MaxFaces.of_graph (VertexSum.simple GL GR cL.1)
    (VertexSum.connected cL cR) (VertexSum.legal ..) hn
  have left : MaxFaces (@tail nL esL) (reversal GL) l :=
    (MaxFaces.congr (split nL esL) (origins nL esL) (reverse GL)).mpr hl
  have right : MaxFaces (@tail nR esR) (reversal GR) r :=
    (MaxFaces.congr (split nR esR) (origins nR esR) (reverse GR)).mpr hr
  have joined : MaxFaces (@jointTail nL nR esL esR) ((reversal GL).sumCongr (reversal GR)) k :=
    (MaxFaces.congr (joint GL GR cL.1) (joint_origins GL GR cL.1) (joint_reverse GL GR cL.1)).mpr hk
  have faces := MaxFaces.vertex_sum tag tag (reversal GL) (reversal GR) left right joined
  rw [VertexSum.length_edges] at ek
  omega

end HoG.Blocks
