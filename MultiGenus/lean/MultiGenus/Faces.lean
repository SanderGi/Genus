/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.List.Iterate
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Order.Setoid.Basic

/-! # Facial walks of a rotation system

Each dart records its origin and destination. Reversing a dart and then moving to
the cyclic successor at its new origin traces the boundary of a face.
-/

@[expose] public section

namespace MultiGenus.Faces

/-- The cyclic neighbor list at a vertex, with an empty list outside the vertex range. -/
def row (rows : List (List Nat)) (u : Nat) : List Nat := rows.getD u []

/-- Each row orders distinct neighbors in the vertex range, and adjacency is symmetric. -/
structure Valid (rows : List (List Nat)) : Prop where
  bounded : ∀ {u v : Nat}, v ∈ row rows u → v < rows.length
  symmetric : ∀ {u v : Nat}, v ∈ row rows u → u ∈ row rows v
  nodup : ∀ u : Nat, (row rows u).Nodup

/-- The finite set of directed incidences in the rows. -/
def darts (rows : List (List Nat)) : Finset (Nat × Nat) :=
  (Finset.range rows.length).biUnion fun u => (row rows u).toFinset.image (u, ·)

@[simp]
theorem mem_darts {rows : List (List Nat)} {u v : Nat} :
    (u, v) ∈ darts rows ↔ u < rows.length ∧ v ∈ row rows u := by
  simp [darts]

/-- The number of darts is the sum of the degrees in the rows. -/
theorem card_darts {rows : List (List Nat)} (h : Valid rows) :
    (darts rows).card = ∑ u ∈ Finset.range rows.length, (row rows u).length := by
  rw [darts, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro u _
    rw [Finset.card_image_of_injective _ (fun _ _ e => congrArg Prod.snd e),
      List.toFinset_card_of_nodup (h.nodup u)]
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    rintro _ hx hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, _, e⟩ := Finset.mem_image.mp hy
    exact huv (congrArg Prod.fst e.symm)

/-- A dart with evidence that it belongs to the rotation system. -/
abbrev Dart (rows : List (List Nat)) := ↥(darts rows)

/-- Reverse the orientation of an edge. -/
def alpha {rows : List (List Nat)} (h : Valid rows) : Equiv.Perm (Dart rows) :=
  Equiv.mk (fun d => ⟨d.val.swap, mem_darts.mpr
    ⟨h.bounded (mem_darts.mp d.prop).2, h.symmetric (mem_darts.mp d.prop).2⟩⟩)
    (fun d => ⟨d.val.swap, mem_darts.mpr
      ⟨h.bounded (mem_darts.mp d.prop).2, h.symmetric (mem_darts.mp d.prop).2⟩⟩)
    (fun _ => rfl) (fun _ => rfl)

/-- Rotate the outgoing darts of each vertex in its given row order. -/
def rho (rows : List (List Nat)) : Equiv.Perm (Dart rows) where
  toFun d := ⟨(d.val.1, (row rows d.val.1).formPerm d.val.2),
    mem_darts.mpr ⟨(mem_darts.mp d.prop).1,
      List.formPerm_apply_mem_of_mem (mem_darts.mp d.prop).2⟩⟩
  invFun d := ⟨(d.val.1, (row rows d.val.1).formPerm.symm d.val.2),
    mem_darts.mpr ⟨(mem_darts.mp d.prop).1,
      List.mem_of_formPerm_apply_mem (by simpa using (mem_darts.mp d.prop).2)⟩⟩
  left_inv d := Subtype.ext <| Prod.ext rfl (Equiv.symm_apply_apply _ _)
  right_inv d := Subtype.ext <| Prod.ext rfl (Equiv.apply_symm_apply _ _)

@[simp] theorem alpha_apply {rows : List (List Nat)} (h : Valid rows) (d : Dart rows) :
    (alpha h d).val = d.val.swap := rfl

@[simp] theorem rho_apply (rows : List (List Nat)) (d : Dart rows) :
    (rho rows d).val = (d.val.1, (row rows d.val.1).formPerm d.val.2) := rfl

@[simp] theorem rho_symm_apply (rows : List (List Nat)) (d : Dart rows) :
    ((rho rows).symm d).val = (d.val.1, (row rows d.val.1).formPerm.symm d.val.2) := rfl

/-- Face tracing as a permutation of the valid darts. -/
def facePerm {rows : List (List Nat)} (h : Valid rows) : Equiv.Perm (Dart rows) :=
  rho rows * alpha h

/-- Cross the current edge and take its cyclic successor in the destination row. -/
def faceStep (rows : List (List Nat)) (d : Nat × Nat) : Nat × Nat :=
  (d.2, (row rows d.2).formPerm d.1)

@[simp]
theorem facePerm_apply {rows : List (List Nat)} (h : Valid rows) (d : Dart rows) :
    (facePerm h d).val = faceStep rows d.val := rfl

/-- At position `i`, the next dart uses position `(i+1) % degree`, including wraparound. -/
theorem faceStep_getElem {rows : List (List Nat)} (h : Valid rows) (v i : Nat)
    (hi : i < (row rows v).length) :
    faceStep rows ((row rows v)[i], v) =
      (v, (row rows v)[(i + 1) % (row rows v).length]'(Nat.mod_lt _ (by omega))) := by
  exact congrArg (v, ·) (List.formPerm_apply_getElem _ (h.nodup v) i hi)

private theorem rho_zpow {rows : List (List Nat)} (z : ℤ) (d : Dart rows) :
    ((rho rows ^ z) d).val = (d.val.1, ((row rows d.val.1).formPerm ^ z) d.val.2) := by
  induction z using Int.induction_on generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one]
    simpa only [Equiv.Perm.mul_apply, rho_apply] using ih (d := rho rows d)
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one]
    simpa only [Equiv.Perm.mul_apply, rho_symm_apply, Equiv.Perm.inv_def] using
      ih (d := (rho rows).symm d)

/-- The cycles of the vertex rotation are exactly the nonempty origin fibers. -/
theorem rho_sameCycle_iff {rows : List (List Nat)} (h : Valid rows) (x y : Dart rows) :
    (rho rows).SameCycle x y ↔ x.val.1 = y.val.1 := by
  constructor
  · rintro ⟨n, rfl⟩
    rw [rho_zpow]
  · intro e
    have hy := (mem_darts.mp y.prop).2
    rw [← e] at hy
    obtain ⟨n, hn⟩ := (h.nodup x.val.1).isCycleOn_formPerm.2 (mem_darts.mp x.prop).2 hy
    exact ⟨n, Subtype.ext ((rho_zpow n x).trans (Prod.ext e hn))⟩

/-- All darts visited in the first `number of darts` steps, starting at a dart. -/
def faceWalk (rows : List (List Nat)) (d : Nat × Nat) : Finset (Nat × Nat) :=
  (List.iterate (faceStep rows) d (darts rows).card).toFinset

/-- Number of distinct facial walks, including singleton orbits. -/
def orbitCount (rows : List (List Nat)) : Nat := ((darts rows).image (faceWalk rows)).card

/-- Number of faces of a connected rotation system, including the unique face of a lone vertex. -/
def faceCount (rows : List (List Nat)) : Nat := if rows = [[]] then 1 else orbitCount rows

@[simp] theorem faceCount_isolated : faceCount [[]] = 1 := rfl

private theorem pow_val {rows : List (List Nat)} (h : Valid rows) (n : Nat) (x : Dart rows) :
    ((facePerm h ^ n) x).val = (faceStep rows)^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, facePerm_apply, ih,
      Function.iterate_succ_apply']

/-- The bounded walk visits precisely the darts in the mathematical permutation cycle. -/
theorem mem_faceWalk {rows : List (List Nat)} (h : Valid rows) (x : Dart rows) (z : Nat × Nat) :
    z ∈ faceWalk rows x.val ↔ ∃ y : Dart rows, y.val = z ∧ (facePerm h).SameCycle x y := by
  rw [faceWalk, List.mem_toFinset, List.mem_iterate]
  constructor
  · rintro ⟨n, _, rfl⟩
    exact ⟨(facePerm h ^ n) x, pow_val h n x, n, by rw [zpow_natCast]⟩
  · rintro ⟨y, rfl, hxy⟩
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    let f := facePerm h
    let k := Function.minimalPeriod f x
    have hpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts
      (f.injective.mem_periodicPts x)
    have hbound : k ≤ (darts rows).card := by
      simpa [k] using (Function.minimalPeriod_le_card (f := (f : Dart rows → Dart rows)) (x := x))
    refine ⟨n % k, lt_of_lt_of_le (Nat.mod_lt n hpos) hbound, ?_⟩
    rw [← pow_val h, ← hn]
    exact congrArg Subtype.val (Function.iterate_mod_minimalPeriod_eq (f := f) (x := x)).symm

private theorem faceWalk_eq_iff {rows : List (List Nat)} (h : Valid rows) (x y : Dart rows) :
    faceWalk rows x.val = faceWalk rows y.val ↔ (facePerm h).SameCycle x y := by
  constructor
  · intro e
    have hy := (mem_faceWalk h y y.val).2 ⟨y, rfl, .rfl⟩
    rw [← e, mem_faceWalk h] at hy
    obtain ⟨y', he, hxy⟩ := hy
    exact Subtype.ext he ▸ hxy
  · intro hxy
    ext z
    simp only [mem_faceWalk h]
    exact exists_congr fun d => and_congr_right fun _ =>
      ⟨hxy.symm.trans, hxy.trans⟩

/-- The executable orbit count equals the number of equivalence classes of the face permutation. -/
theorem orbitCount_eq {rows : List (List Nat)} (h : Valid rows) :
    orbitCount rows = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (facePerm h))) := by
  let keys := (darts rows).image (faceWalk rows)
  let key (d : Dart rows) : ↥keys := ⟨faceWalk rows d.val, Finset.mem_image_of_mem _ d.prop⟩
  have surj : Function.Surjective key := by
    intro k
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp k.prop
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let e : Quotient (Equiv.Perm.SameCycle.setoid (facePerm h)) ≃ ↥keys :=
    (Quotient.congrRight (r' := Setoid.ker key) fun x y =>
      (faceWalk_eq_iff h x y).symm.trans
        (show (key x).val = (key y).val ↔ key x = key y from Subtype.ext_iff.symm)).trans
      (Setoid.quotientKerEquivOfSurjective key surj)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-- Face count with the connected edgeless case separated from dart orbits. -/
theorem faceCount_eq {rows : List (List Nat)} (h : Valid rows) :
    faceCount rows = if rows = [[]] then 1
      else Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (facePerm h))) := by
  simp only [faceCount, orbitCount_eq h]

end MultiGenus.Faces
