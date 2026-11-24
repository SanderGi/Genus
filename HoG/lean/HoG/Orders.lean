/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Cut
public import MultiGenus.Reduction
import Mathlib.GroupTheory.Perm.Finite

/-! # Transport and disjoint union of cyclic vertex orders -/

public section

namespace HoG.Orders

open Equiv Equiv.Perm MultiGenus.Reduction

variable {A B V W : Type*}

/-- Conjugating a permutation transports its ordered fibers along any bijection of darts
that preserves and reflects equality of origins. -/
theorem ordered_congr (e : A ≃ B) (tail : A → V) (tail' : B → W)
    (h : ∀ x y, tail x = tail y ↔ tail' (e x) = tail' (e y)) (p : Perm A) :
    Ordered tail p ↔ Ordered tail' (e.permCongr p) := by
  have step (z : Int) (x : A) : ((e.permCongr p) ^ z) (e x) = e ((p ^ z) x) := by
    change (e.permCongrHom p ^ z) (e x) = _
    rw [← map_zpow]
    exact congrArg (fun t => e ((p ^ z) t)) (e.symm_apply_apply x)
  have same (x y : A) : (e.permCongr p).SameCycle (e x) (e y) ↔ p.SameCycle x y := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, e.injective ((step z x).symm.trans hz)⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, (step z x).trans (congrArg e hz)⟩
  constructor
  · rintro hp x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact (same x y).trans ((hp x y).trans (h x y))
  · intro hp x y
    exact (same x y).symm.trans ((hp _ _).trans (h x y).symm)

variable [Finite A] [Finite B]

private theorem same_left (l : Perm A) (r : Perm B) (x y : A) :
    (l.sumCongr r).SameCycle (.inl x) (.inl y) ↔ l.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Cut.sum_pow_left] at hk
    exact ⟨k, by rw [zpow_natCast]; exact Sum.inl.inj hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [zpow_natCast, Cut.sum_pow_left, hk]⟩

private theorem same_right (l : Perm A) (r : Perm B) (x y : B) :
    (l.sumCongr r).SameCycle (.inr x) (.inr y) ↔ r.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Cut.sum_pow_right] at hk
    exact ⟨k, by rw [zpow_natCast]; exact Sum.inr.inj hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [zpow_natCast, Cut.sum_pow_right, hk]⟩

private theorem separate (l : Perm A) (r : Perm B) (x : A) (y : B) :
    ¬(l.sumCongr r).SameCycle (.inl x) (.inr y) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [Cut.sum_pow_left] at hk
  contradiction

/-- Independent cyclic orders on the tagged origin fibers are exactly disjoint sums of
orders on the two components, allowing either component to have no darts. -/
theorem ordered_sum_iff (f : A → V) (g : B → W) {p : Perm (A ⊕ B)} :
    Ordered (Sum.map f g) p ↔ ∃ l r, Ordered f l ∧ Ordered g r ∧ p = l.sumCongr r := by
  constructor
  · intro ord
    have maps : Set.MapsTo p (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨x, rfl⟩
      have key := (ord (.inl x) _).mp SameCycle.rfl.apply_right
      cases eq : p (.inl x) with
      | inl a => exact ⟨a, rfl⟩
      | inr b => rw [eq] at key; contradiction
    obtain ⟨⟨l,r⟩, eq⟩ := mem_sumCongrHom_range_of_perm_mapsTo_inl maps
    change l.sumCongr r = p at eq
    subst p
    refine ⟨l, r, ?_, ?_, rfl⟩
    · intro x y
      simpa only [Sum.map_inl, Sum.inl.injEq] using
        (same_left l r x y).symm.trans (ord (.inl x) (.inl y))
    · intro x y
      simpa only [Sum.map_inr, Sum.inr.injEq] using
        (same_right l r x y).symm.trans (ord (.inr x) (.inr y))
  · rintro ⟨l,r,hl,hr,rfl⟩ (x | x) (y | y)
    · simpa only [Sum.map_inl, Sum.inl.injEq] using (same_left l r x y).trans (hl x y)
    · exact ⟨fun h => (separate l r x y h).elim, fun h => nomatch h⟩
    · exact ⟨fun h => (separate l r y x h.symm).elim, fun h => nomatch h⟩
    · simpa only [Sum.map_inr, Sum.inr.injEq] using (same_right l r x y).trans (hr x y)

end HoG.Orders
