/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.VertexSum

/-! # Dart coordinates at the common vertex of a block sum -/

@[expose] public section

namespace HoG.BlockCoordinates

open MultiGenus MultiGenus.Rotations

/-- Darts whose source is the distinguished vertex. -/
abbrev Root (n : Nat) (es : List Edge) := {d : VertexSum.Darts n es // d.val.1 = 0}

/-- Darts sourced at vertices away from the distinguished vertex. -/
abbrev Other (n : Nat) (es : List Edge) := {d : VertexSum.Darts n es // d.val.1 ≠ 0}

/-- Forget the root/interior tag and recover the original dart. -/
def split (n : Nat) (es : List Edge) : Root n es ⊕ Other n es ≃ VertexSum.Darts n es :=
  Equiv.sumCompl (fun d : VertexSum.Darts n es => d.val.1 = 0)

/-- Ordinary vertex label of an interior dart. -/
def tag {n es} (x : Other n es) := x.val.val.1

/-- Read the origin in root/interior coordinates. -/
def tail {n es} : Root n es ⊕ Other n es → Unit ⊕ Nat := Sum.map (fun _ => ()) tag

/-- Reversal transported into the root/interior coordinates. -/
def reversal {n es} (G : SimpleInput n es) : Equiv.Perm (Root n es ⊕ Other n es) :=
  (split n es).symm.permCongr (VertexSum.rev G)

theorem origins (n : Nat) (es : List Edge) (x y : Root n es ⊕ Other n es) :
    tail x = tail y ↔ (split n es x).val.1 = (split n es y).val.1 := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [tail, Sum.map_inl, Sum.map_inr, split, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, tag] <;> grind [x.prop, y.prop]

theorem reverse {n es} (G : SimpleInput n es) (x : Root n es ⊕ Other n es) :
    split n es (reversal G x) = VertexSum.rev G (split n es x) := by
  simp [reversal, Equiv.permCongr_apply]

/-- In a connected graph with another vertex there is a dart leaving the root. -/
theorem root_nonempty {n es} (G : SimpleInput n es) (con : ConnectedInput n es) (hn : 1 < n) :
    Nonempty (Root n es) := by
  obtain ⟨v, hv⟩ := SimpleInput.exists_neighbor con hn 0 con.1
  exact ⟨⟨⟨(0,v), (VertexSum.dart_iff_adj G _ _).mpr hv⟩, rfl⟩⟩

/-- First forget the two root/interior tags, then include the component darts into the
concrete vertex sum. -/
noncomputable def joint {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) :
    (Root nL esL ⊕ Other nL esL) ⊕ (Root nR esR ⊕ Other nR esR) ≃
      VertexSum.Darts (VertexSum.vertices nL nR) (VertexSum.edges nL esL esR) :=
  ((split nL esL).sumCongr (split nR esR)).trans (VertexSum.dartEquiv GL GR hL)

/-- Arrange both root dart sets first, identify their origins, and retain a component tag
on all interior vertex labels. -/
def jointTail {nL nR esL esR} :
    (Root nL esL ⊕ Other nL esL) ⊕ (Root nR esR ⊕ Other nR esR) → Unit ⊕ (Nat ⊕ Nat) :=
  (Sum.map (fun _ => ()) (Sum.map tag tag)) ∘
    (Equiv.sumSumSumComm (Root nL esL) (Root nR esR) (Other nL esL) (Other nR esR)).symm

private def asOption : Unit ⊕ (Nat ⊕ Nat) → Option (Nat ⊕ Nat) := Sum.elim (fun _ => none) some

private theorem asOption_injective : Function.Injective asOption := by
  rintro (⟨⟩ | x) (⟨⟩ | y) h <;> simp_all [asOption]

private theorem tag_eq {nL nR esL esR}
    (x : (Root nL esL ⊕ Other nL esL) ⊕ (Root nR esR ⊕ Other nR esR)) :
    VertexSum.originTag (((split nL esL).sumCongr (split nR esR)) x) =
      asOption (jointTail x) := by
  rcases x with (x | x) | (x | x) <;>
    simp [VertexSum.originTag, split, x.prop, jointTail, tag, asOption]

/-- The joint coordinate model has exactly the concrete vertex fibers. -/
theorem joint_origins {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x y : (Root nL esL ⊕ Other nL esL) ⊕ (Root nR esR ⊕ Other nR esR)) :
    jointTail x = jointTail y ↔ (joint GL GR hL x).val.1 = (joint GL GR hL y).val.1 := by
  exact asOption_injective.eq_iff.symm.trans (((tag_eq x).symm ▸ (tag_eq y).symm ▸
    VertexSum.origins GL GR hL _ _))

/-- The joint dart equivalence takes the independent component reversals to the concrete
reversal of the combined graph. -/
theorem joint_reverse {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x : (Root nL esL ⊕ Other nL esL) ⊕ (Root nR esR ⊕ Other nR esR)) :
    joint GL GR hL (((reversal GL).sumCongr (reversal GR)) x) =
      VertexSum.rev (VertexSum.simple GL GR hL) (joint GL GR hL x) := by
  unfold joint
  rw [Equiv.trans_apply, Equiv.trans_apply, ← VertexSum.reverse]
  apply congrArg
  cases x with
  | inl x => exact congrArg Sum.inl (reverse GL x)
  | inr x => exact congrArg Sum.inr (reverse GR x)

end HoG.BlockCoordinates
