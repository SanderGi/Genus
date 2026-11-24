/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySubdivide
import Mathlib.Data.Fintype.Sum

/-! # First return to the darts at a cut vertex -/

@[expose] public section

namespace HoG.Cut

open Equiv Equiv.Perm MultiGenus.Surgery

variable {D B C : Type*}

/-- A landing at a boundary dart changes by the new boundary rotation. All other steps persist. -/
structure Rewire (i : B → D) (p q : Perm D) (r : Perm B) : Prop where
  hit : ∀ x b, p x = i b → q x = i (r b)
  miss : ∀ x, (∀ b, p x ≠ i b) → q x = p x

/-- The marked-to-marked segments of a permutation, together with its unmarked cycles.
`len b` counts the internal darts after boundary dart `b` before the next marked landing. -/
structure Chart (p : Perm D) (i : B → D) (C : Type*) where
  /-- First marked dart reached after leaving each marked dart. -/
  ret : Perm B
  /-- Number of unmarked darts strictly between departure and first return. -/
  len : B → Nat
  finish : ∀ b, (p ^ (len b + 1)) (i b) = i (ret b)
  interior : ∀ b k, 0 < k → k ≤ len b → ∀ a, (p ^ k) (i b) ≠ i a
  /-- Successor on the darts of faces disjoint from the cut vertex. -/
  inner : Perm C
  /-- Original dart corresponding to a dart on a face disjoint from the cut. -/
  point : C → D
  free : ∀ c b, point c ≠ i b
  move : ∀ c, p (point c) = point (inner c)
  /-- Identify the departing boundary dart of a segment, or the dart on a disjoint face. -/
  locate : D → B ⊕ C
  segment : ∀ b k, k ≤ len b → locate ((p ^ k) (i b)) = .inl b
  closed : ∀ c, locate (point c) = .inr c
  cover : ∀ x, (∃ b k, k ≤ len b ∧ (p ^ k) (i b) = x) ∨ ∃ c, point c = x

theorem cancel_steps (p : Perm D) {x y : D} {k j : Nat} (le : k ≤ j)
    (eq : (p ^ j) x = (p ^ k) y) : (p ^ (j - k)) x = y := by
  apply (p ^ k).injective
  rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_of_le le]
  exact eq

/-- Darts on cycles that never encounter the boundary. -/
abbrev Closed (p : Perm D) (i : B → D) := {x : D // ¬ ∃ b, p.SameCycle (i b) x}

/-- Every finite permutation admits a first-return chart at any set of distinct marked darts. -/
noncomputable def firstReturn [Finite D] [Finite B] (p : Perm D) (i : B ↪ D) :
    Chart p i (Closed p i) := by
  classical
  have again (b : B) : ∃ k : Nat, ∃ a, (p ^ (k + 1)) (i b) = i a := by
    obtain ⟨k, hk⟩ := ((SameCycle.refl p (i b)).apply_left).exists_nat_pow_eq
    exact ⟨k, b, by rwa [pow_succ, Perm.mul_apply]⟩
  let len (b : B) := Nat.find (again b)
  let next (b : B) := (Nat.find_spec (again b)).choose
  have finish (b : B) : (p ^ (len b + 1)) (i b) = i (next b) :=
    (Nat.find_spec (again b)).choose_spec
  have interior (b : B) (k : Nat) (pos : 0 < k) (le : k ≤ len b) (a : B) :
      (p ^ k) (i b) ≠ i a := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    exact fun eq => Nat.find_min (again b) (show k < len b by omega) ⟨a, eq⟩
  have compare {a b : B} {j k : Nat} (eq : (p ^ j) (i a) = (p ^ k) (i b))
      (lt : k < j) (short : j - k ≤ len a) : False :=
    interior a (j-k) (by omega) short b (cancel_steps p lt.le eq)
  have inj : Function.Injective next := by
    intro a b eq
    have land := (finish a).trans ((congrArg i eq).trans (finish b).symm)
    rcases lt_trichotomy (len a) (len b) with lt | same | lt
    · exact (compare land.symm (by omega) (by omega)).elim
    · rw [same] at land
      exact i.injective ((p ^ (len b + 1)).injective land)
    · exact (compare land (by omega) (by omega)).elim
  let ret := Equiv.ofBijective next ⟨inj, Finite.surjective_of_injective inj⟩
  let visits (x : D) (b : B) := ∃ k, k ≤ len b ∧ (p ^ k) (i b) = x
  have unique {x : D} {a b : B} (ha : visits x a) (hb : visits x b) : a = b := by
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨k, hk, eq⟩ := hb
    rcases lt_trichotomy k j with lt | rfl | lt
    · exact (compare eq.symm lt (by omega)).elim
    · exact i.injective ((p ^ k).injective eq.symm)
    · exact (compare eq lt (by omega)).elim
  have covered (x : D) : (∃ b, visits x b) ↔ ∃ b, p.SameCycle (i b) x := by
    constructor
    · rintro ⟨b, k, _, eq⟩
      exact ⟨b, k, by rwa [zpow_natCast]⟩
    · rintro ⟨b, hb⟩
      obtain ⟨k, hk⟩ := hb.exists_nat_pow_eq
      have ex : ∃ j : Nat, ∃ a, (p ^ j) (i a) = x := ⟨k, b, hk⟩
      let j := Nat.find ex
      obtain ⟨a, ha⟩ := Nat.find_spec ex
      change (p ^ j) (i a) = x at ha
      refine ⟨a, j, ?_, ha⟩
      by_contra! lt
      apply Nat.find_min ex (m := j - (len a + 1)) (show j - (len a + 1) < j by omega)
      refine ⟨next a, ?_⟩
      rw [← finish a, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel lt]
      exact ha
  let locate (x : D) : B ⊕ Closed p i :=
    if h : ∃ b, visits x b then .inl h.choose else .inr ⟨x, fun t => h ((covered x).mpr t)⟩
  have atC (z : Closed p i) : locate z.val = .inr z := by
    simp only [locate, show ¬ ∃ b, visits z.val b from fun h => z.prop ((covered _).mp h),
      ↓reduceDIte]
  let inner : Perm (Closed p i) := p.subtypePerm fun x => by
    simp
  refine ⟨ret, len, finish, interior, inner, Subtype.val, ?_, fun _ => rfl, locate, ?_, atC, ?_⟩
  · intro z b eq
    exact z.prop ⟨b, eq ▸ SameCycle.rfl⟩
  · intro b k le
    have h : visits ((p ^ k) (i b)) b := ⟨k, le, rfl⟩
    have ex : ∃ a, visits ((p ^ k) (i b)) a := ⟨b, h⟩
    simp only [locate, ex, ↓reduceDIte, Sum.inl.injEq]
    exact unique ex.choose_spec h
  · intro x
    by_cases h : ∃ b, visits x b
    · exact Or.inl h
    · exact Or.inr ⟨⟨x, fun t => h ((covered x).mpr t)⟩, rfl⟩

theorem sum_pow_left {A E : Type*} (p : Perm A) (q : Perm E) (k : Nat) (a : A) :
    (p.sumCongr q ^ k) (.inl a) = .inl ((p ^ k) a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]; rfl

theorem sum_pow_right {A E : Type*} (p : Perm A) (q : Perm E) (k : Nat) (a : E) :
    (p.sumCongr q ^ k) (.inr a) = .inr ((q ^ k) a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]; rfl

/-- The orbits of a disjoint sum are the disjoint union of the two orbit quotients. -/
theorem countCycles_sum [Finite D] [Finite B] (p : Perm D) (q : Perm B) :
    countCycles (p.sumCongr q) = countCycles p + countCycles q := by
  classical
  let lp := SameCycle.setoid p
  let rp := SameCycle.setoid q
  let sp := SameCycle.setoid (p.sumCongr q)
  let key : D ⊕ B → Quotient lp ⊕ Quotient rp := Sum.map (Quotient.mk lp) (Quotient.mk rp)
  have rel (x y) : (p.sumCongr q).SameCycle x y ↔ key x = key y := by
    constructor
    · intro h
      obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
      cases x with
      | inl a =>
        rw [sum_pow_left]
        exact congrArg Sum.inl (Quotient.sound (show p.SameCycle a ((p ^ k) a) from
          ⟨k, by rw [zpow_natCast]⟩))
      | inr a =>
        rw [sum_pow_right]
        exact congrArg Sum.inr (Quotient.sound (show q.SameCycle a ((q ^ k) a) from
          ⟨k, by rw [zpow_natCast]⟩))
    · cases x with
      | inl a =>
        rintro h
        cases y with
        | inl b =>
          have hab : p.SameCycle a b := Quotient.exact (Sum.inl.inj h)
          obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
          exact ⟨k, by rw [zpow_natCast, sum_pow_left, hk]⟩
        | inr b => cases h
      | inr a =>
        rintro h
        cases y with
        | inl b => cases h
        | inr b =>
          have hab : q.SameCycle a b := Quotient.exact (Sum.inr.inj h)
          obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
          exact ⟨k, by rw [zpow_natCast, sum_pow_right, hk]⟩
  have surj : Function.Surjective key := by
    rintro (a | b)
    · exact ⟨.inl a.out, congrArg Sum.inl (Quotient.out_eq a)⟩
    · exact ⟨.inr b.out, congrArg Sum.inr (Quotient.out_eq b)⟩
  let e := (Quotient.congrRight (r := sp) (r' := Setoid.ker key) rel).trans
    (Setoid.quotientKerEquivOfSurjective key surj)
  exact (Nat.card_congr e).trans Nat.card_sum

namespace Chart

variable {p q : Perm D} {i : B → D}

/-- Sewing an arbitrary boundary rotation changes only the permutation of returning segments. -/
theorem count [Finite D] [Finite B] [Finite C] (s : Chart p i C)
    (r : Perm B) (w : Rewire i p q r) :
    countCycles q = countCycles (r * s.ret) + countCycles s.inner := by
  let t := (r * s.ret).sumCongr s.inner
  let expand : B ⊕ C → D := Sum.elim i s.point
  have start (b : B) : s.locate (i b) = .inl b := s.segment b 0 (Nat.zero_le _)
  have walk (b : B) (k : Nat) (le : k ≤ s.len b) : (q ^ k) (i b) = (p ^ k) (i b) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih (by omega)]
      apply w.miss
      simpa only [pow_succ', Perm.mul_apply] using s.interior b (k+1) (by omega) le
  have endWalk (b : B) : (q ^ (s.len b + 1)) (i b) = i (r (s.ret b)) := by
    rw [pow_succ', Perm.mul_apply, walk _ _ le_rfl]
    exact w.hit _ _ (by simpa only [pow_succ', Perm.mul_apply] using s.finish b)
  have stepC (c : C) : q (s.point c) = s.point (s.inner c) :=
    (w.miss _ (fun b => s.move c ▸ s.free (s.inner c) b)).trans (s.move c)
  let e := quotientEquivOfRetraction t q expand s.locate (by
    rintro (b | c)
    · exact start b
    · exact s.closed c) (by
    rintro (b | c)
    · exact ⟨((s.len b + 1 : Nat) : ℤ), by rw [zpow_natCast]; exact endWalk b⟩
    · change q.SameCycle (s.point c) (s.point (s.inner c))
      rw [← stepC]
      exact SameCycle.rfl.apply_right) (by
    intro x
    rcases s.cover x with ⟨b, k, le, rfl⟩ | ⟨c, rfl⟩
    · rw [s.segment b k le, ← walk b k le, ← Perm.mul_apply, ← pow_succ']
      by_cases h : k = s.len b
      · rw [h, endWalk, start]
        exact (SameCycle.refl t (.inl b)).apply_right
      · rw [walk b (k+1) (by omega), s.segment _ _ (by omega)]
    · rw [stepC, s.closed, s.closed]
      exact (SameCycle.refl t (.inr c)).apply_right) (by
    intro x
    rcases s.cover x with ⟨b, k, le, rfl⟩ | ⟨c, rfl⟩
    · rw [s.segment b k le, ← walk b k le]
      exact ⟨k, by rw [zpow_natCast]; rfl⟩
    · rw [s.closed]
      exact SameCycle.rfl)
  exact (Nat.card_congr e).trans (countCycles_sum _ _)

/-- Taking the cut in two disjoint pieces preserves their separate return maps and closed faces. -/
noncomputable def sum {E A F : Type*} {q : Perm E} {j : A → E} (s : Chart p i C)
    (t : Chart q j F) : Chart (p.sumCongr q) (Sum.map i j) (C ⊕ F) where
  ret := s.ret.sumCongr t.ret
  len := Sum.elim s.len t.len
  finish := by
    rintro (b | a)
    · exact (sum_pow_left ..).trans (congrArg Sum.inl (s.finish b))
    · exact (sum_pow_right ..).trans (congrArg Sum.inr (t.finish a))
  interior := by
    rintro (b | a) k pos le (b' | a')
    · change (p.sumCongr q ^ k) (.inl _) ≠ .inl _
      rw [sum_pow_left]
      exact fun h => s.interior b k pos le b' (Sum.inl.inj h)
    · simp only [Sum.map_inl, Sum.map_inr, sum_pow_left, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [Sum.map_inl, Sum.map_inr, sum_pow_right, ne_eq, reduceCtorEq, not_false_eq_true]
    · change (p.sumCongr q ^ k) (.inr _) ≠ .inr _
      rw [sum_pow_right]
      exact fun h => t.interior a k pos le a' (Sum.inr.inj h)
  inner := s.inner.sumCongr t.inner
  point := Sum.map s.point t.point
  free := by
    rintro (x | y) (b | a)
    · exact fun eq => s.free x b (Sum.inl.inj eq)
    · exact Sum.inl_ne_inr
    · exact Sum.inr_ne_inl
    · exact fun eq => t.free y a (Sum.inr.inj eq)
  move := by
    rintro (x | y)
    · exact congrArg Sum.inl (s.move x)
    · exact congrArg Sum.inr (t.move y)
  locate := Sum.elim (Sum.map Sum.inl Sum.inl ∘ s.locate) (Sum.map Sum.inr Sum.inr ∘ t.locate)
  segment := by
    rintro (b | a) k le
    · simp only [Sum.map_inl, sum_pow_left, Sum.elim_inl, Function.comp_apply, s.segment b k le]
    · simp only [Sum.map_inr, sum_pow_right, Sum.elim_inr, Function.comp_apply, t.segment a k le,
        Sum.map_inl]
  closed := by
    rintro (x | y)
    · simp [s.closed x]
    · simp [t.closed y]
  cover := by
    rintro (x | y)
    · rcases s.cover x with ⟨b, k, le, rfl⟩ | ⟨c, rfl⟩
      · exact Or.inl ⟨.inl b, k, le, sum_pow_left ..⟩
      · exact Or.inr ⟨.inl c, rfl⟩
    · rcases t.cover y with ⟨a, k, le, rfl⟩ | ⟨c, rfl⟩
      · exact Or.inl ⟨.inr a, k, le, sum_pow_right ..⟩
      · exact Or.inr ⟨.inr c, rfl⟩

end Chart
end HoG.Cut
