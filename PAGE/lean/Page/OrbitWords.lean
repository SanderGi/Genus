/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import MultiGenus.Genus
import Mathlib.Data.List.GetD

/-! # Cyclic dart words for a finite permutation -/

@[expose] public section

namespace Page.OrbitWords

open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Write one orbit cyclically, retaining a singleton when the permutation fixes its dart. -/
noncomputable def word (p : Perm D) (x : D) : List D :=
  if p x = x then [x] else p.toList x

theorem mem_word (p : Perm D) (x y : D) : y ∈ word p x ↔ p.SameCycle x y := by
  by_cases h : p x = x
  · simp only [word, h, ↓reduceIte, List.mem_singleton]
    exact ⟨by rintro rfl; exact .rfl, fun hs => (hs.eq_of_left h).symm⟩
  · simp [word, mem_toList_iff, mem_support, h]

theorem nodup_word (p : Perm D) (x : D) : (word p x).Nodup := by
  unfold word
  split <;> simp [nodup_toList]

theorem step_word (p : Perm D) (x y : D) (hy : y ∈ word p x) :
    (word p x).formPerm y = p y := by
  by_cases h : p x = x
  · have : y = x := by simpa [word, h] using hy
    subst y
    simp [word, h]
  · simpa only [word, h, ↓reduceIte, formPerm_toList] using ((mem_word p x y).mp hy).cycleOf_apply

/-- Mapping distinct letters through an injection transports their cyclic successor. -/
theorem formPerm_map_apply {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (inj : Function.Injective f) (w : List A) (nd : w.Nodup) (x : A) (hx : x ∈ w) :
    (w.map f).formPerm (f x) = f (w.formPerm x) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hm : i < (w.map f).length := by simpa using hi
  rw [← List.getElem_map (f := f) (h := hm), List.formPerm_apply_getElem _ (nd.map inj) i hm,
    List.formPerm_apply_getElem _ nd i hi]
  simp

/-- One representative word per orbit, indexed by the orbit quotient. -/
noncomputable def words (p : Perm D) : List (List D) := by
  classical
  exact ((Finset.univ : Finset (Quotient (SameCycle.setoid p))).toList).map fun c =>
    word p c.out

theorem length_words (p : Perm D) :
    (words p).length = Nat.card (Quotient (SameCycle.setoid p)) := by
  classical
  simp [words, Nat.card_eq_fintype_card]

theorem mem_words (p : Perm D) (w : List D) :
    w ∈ words p ↔ ∃ c : Quotient (SameCycle.setoid p), w = word p c.out := by
  classical
  simp [words, eq_comm]

theorem mem_flatten_words (p : Perm D) (x : D) : x ∈ (words p).flatten := by
  let c : Quotient (SameCycle.setoid p) := Quotient.mk _ x
  refine List.mem_flatten.mpr ⟨_, (mem_words p _).mpr ⟨c, rfl⟩, (mem_word ..).mpr ?_⟩
  exact Quotient.exact (Quotient.out_eq c)

theorem nodup_flatten_words (p : Perm D) : (words p).flatten.Nodup := by
  classical
  change List.Pairwise (· ≠ ·) _
  rw [List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨c, rfl⟩ := (mem_words p w).mp hw
    exact nodup_word _ _
  · rw [words, List.pairwise_map]
    apply List.Pairwise.imp _ (Finset.univ : Finset (Quotient (SameCycle.setoid p))).nodup_toList
    intro c d hcd x hx y hy hxy
    subst y
    apply hcd
    have hs := ((mem_word ..).mp hx).trans ((mem_word ..).mp hy).symm
    exact (Quotient.out_eq c).symm.trans ((Quotient.sound hs).trans (Quotient.out_eq d))

end Page.OrbitWords
