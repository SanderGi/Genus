/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Excursions
public import HoG.Orders
public import MultiGenus.Representation

/-! # Maximal face counts under vertex identification -/

@[expose] public section

namespace HoG

open Equiv Equiv.Perm MultiGenus MultiGenus.Reduction MultiGenus.Surgery

/-- The largest face count of a vertex rotation with the given origins and edge reversal. -/
structure MaxFaces {D V : Type*} (tail : D → V) (rev : Perm D) (k : Nat) : Prop where
  attains : ∃ p, Ordered tail p ∧ countCycles (p * rev) = k
  upper : ∀ p, Ordered tail p → countCycles (p * rev) ≤ k

namespace MaxFaces

variable {D E V W : Type*} [Finite D] [Finite E]

/-- Dart renaming preserves maximality when it respects reversal and vertex fibers. -/
theorem congr {tail : D → V} {other : E → W} {rev : Perm D} {rev' : Perm E} {k : Nat}
    (e : D ≃ E) (fibers : ∀ x y, tail x = tail y ↔ other (e x) = other (e y))
    (reverse : ∀ x, e (rev x) = rev' (e x)) : MaxFaces tail rev k ↔ MaxFaces other rev' k := by
  have track (p : Perm D) : countCycles (p * rev) = countCycles (e.permCongr p * rev') := by
    apply countCycles_congr e
    intro x
    simp [Perm.mul_apply, ← reverse, Equiv.permCongr_apply]
  constructor
  · intro old
    obtain ⟨p, hp, eq⟩ := old.attains
    refine ⟨⟨_, (Orders.ordered_congr e _ _ fibers p).mp hp, (track p).symm.trans eq⟩, ?_⟩
    intro q hq
    obtain ⟨p, rfl⟩ := e.permCongr.surjective q
    rw [← track]
    exact old.upper p ((Orders.ordered_congr e _ _ fibers p).mpr hq)
  · intro new
    obtain ⟨q, hq, eq⟩ := new.attains
    obtain ⟨p, rfl⟩ := e.permCongr.surjective q
    refine ⟨⟨p, (Orders.ordered_congr e _ _ fibers p).mpr hq, (track p).trans eq⟩, ?_⟩
    intro s hs
    rw [track]
    exact new.upper _ ((Orders.ordered_congr e _ _ fibers s).mp hs)

/-- The public minimum has an optimal face count on the darts of any legal presentation. -/
theorem of_graph {n edges rows} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hr : Rotations.Legal n edges rows) (hn : 1 < n) :
    ∃ k, MaxFaces (fun d : Faces.Dart rows => d.val.1) (Faces.alpha (valid_of_legal G hr)) k ∧
      2 + edges.length = n + k + 2 * minimumGenus n edges := by
  have least := Representation.minimumGenus_isLeast_attains G con hr hn
  obtain ⟨p, hp, euler⟩ := least.1
  refine ⟨_, ⟨⟨p, hp, rfl⟩, ?_⟩, euler⟩
  intro q hq
  obtain ⟨g, eq⟩ := eulerExact_darts G con hr hn q hq
  have le := least.2 (show Attains .. from ⟨q, hq, eq⟩)
  omega

section Vertex

variable {A B I J U T : Type*} [Finite A] [Finite B] [Finite I] [Finite J]

private abbrev rootTag (A : Type*) := fun _ : A => ()

omit [Finite A] in
private theorem root_order {r : Perm A} :
    Ordered (rootTag A) r ↔ ∀ x y, r.SameCycle x y := by simp [Ordered, rootTag]

private def tag (f : I → U) (g : J → T) : ((A ⊕ I) ⊕ B ⊕ J) → Unit ⊕ U ⊕ T :=
  Sum.map (rootTag (A ⊕ B)) (Sum.map f g) ∘ (Excursions.regroup A B I J).symm

private theorem join_order (f : I → U) (g : J → T) (p : Perm ((A ⊕ I) ⊕ B ⊕ J)) :
    Ordered (tag f g) p ↔
      ∃ r s t, (∀ x y, r.SameCycle x y) ∧ Ordered f s ∧ Ordered g t ∧
        p = Excursions.join r s t := by
  let e := Excursions.regroup A B I J
  let orig := Sum.map (rootTag (A ⊕ B)) (Sum.map f g)
  have fibers (x y) : orig x = orig y ↔ tag f g (e x) = tag f g (e y) := by
    simp only [tag, Function.comp_apply, e, Equiv.symm_apply_apply]
    rfl
  obtain ⟨z, rfl⟩ := e.permCongr.surjective p
  rw [← Orders.ordered_congr e _ _ fibers, Orders.ordered_sum_iff]
  constructor
  · rintro ⟨r, q, hr, hq, rfl⟩
    obtain ⟨s, t, hs, ht, rfl⟩ := (Orders.ordered_sum_iff f g).mp hq
    exact ⟨r, s, t, root_order.mp hr, hs, ht, rfl⟩
  · rintro ⟨r, s, t, hr, hs, ht, eq⟩
    refine ⟨r, s.sumCongr t, root_order.mpr hr, (Orders.ordered_sum_iff f g).mpr
      ⟨s, t, hs, ht, rfl⟩, e.permCongr.injective eq⟩

/-- Identifying two nonempty roots reduces the maximal total face count by exactly one.
All rotations at the identified vertex are included in the maximum. -/
theorem vertex_sum [Nonempty A] [Nonempty B] (f : I → U) (g : J → T)
    (v : Perm (A ⊕ I)) (w : Perm (B ⊕ J)) {kl kr k}
    (left : MaxFaces (Sum.map (fun _ : A => ()) f) v kl)
    (right : MaxFaces (Sum.map (fun _ : B => ()) g) w kr)
    (whole : MaxFaces (Sum.map (fun _ : A ⊕ B => ()) (Sum.map f g) ∘
      (Excursions.regroup A B I J).symm) (v.sumCongr w) k) : k + 1 = kl + kr := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp, eq⟩ := whole.attains
    obtain ⟨r, s, t, hr, hs, ht, rfl⟩ := (join_order f g p).mp hp
    obtain ⟨a, b, c, ha, hb, _, _, _, upper, sum⟩ := Excursions.fixed_exterior s t v w
    have joint := upper r hr
    have l := left.upper _ ((Orders.ordered_sum_iff _ _).mpr ⟨a, s, root_order.mpr ha, hs, rfl⟩)
    have h := right.upper _ ((Orders.ordered_sum_iff _ _).mpr ⟨b, t, root_order.mpr hb, ht, rfl⟩)
    omega
  · obtain ⟨p, hp, eqL⟩ := left.attains
    obtain ⟨q, hq, eqR⟩ := right.attains
    obtain ⟨l, s, hl, hs, rfl⟩ := (Orders.ordered_sum_iff _ _).mp hp
    obtain ⟨r, t, hr, ht, rfl⟩ := (Orders.ordered_sum_iff _ _).mp hq
    obtain ⟨a, b, c, _, _, hc, leftBound, rightBound, _, sum⟩ := Excursions.fixed_exterior s t v w
    have l' := leftBound l (root_order.mp hl)
    have r' := rightBound r (root_order.mp hr)
    have bound := whole.upper _ ((join_order f g _).mpr ⟨c, s, t, hc, hs, ht, rfl⟩)
    omega

end Vertex
end MaxFaces
end HoG
