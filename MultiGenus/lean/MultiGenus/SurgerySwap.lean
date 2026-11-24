/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Transposing two face successors

Faces are orbits on darts, including singleton orbits. Starting at a cut dart,
follow the old walk until it next meets either cut. Transposing the two targets
preserves the interior of this walk and exchanges its final target.
-/

public section

namespace MultiGenus.Surgery

open Equiv Equiv.Perm

variable {D : Type*}

/-- Number of all orbits of a dart permutation, including fixed darts. -/
@[expose] noncomputable def countCycles (p : Perm D) : ℕ := Nat.card (Quotient (SameCycle.setoid p))

/-- A map taking each step to a walk takes entire finite orbits to orbits. -/
theorem map_sameCycle {E : Type*} [Finite D] (p : Perm D) (g : Perm E) (u : D → E)
    (step : ∀ x, g.SameCycle (u x) (u (p x))) {x y : D} (h : p.SameCycle x y) :
    g.SameCycle (u x) (u y) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using SameCycle.refl g (u x)
  | succ n ih => rw [pow_succ', mul_apply]; exact ih.trans (step _)

private theorem avoids_of_closed [Finite D] (p : Perm D) (a b : D) (k : ℕ)
    (close : (p ^ (k + 1)) a = a) (avoid : ∀ j < k + 1, (p ^ j) a ≠ b) :
    ¬ p.SameCycle a b := by
  rintro h
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  have per : Function.IsPeriodicPt p (k + 1) a := by
    change p^[(k + 1)] a = a
    rwa [← coe_pow]
  have he := per.iterate_mod_apply m
  rw [← coe_pow, ← coe_pow] at he
  exact avoid _ (Nat.mod_lt _ (by omega)) (he.trans hm)

/-- Switching two distinct landing darts puts them in the same orbit exactly when they
were in different orbits before the switch. -/
theorem sameCycle_swap_mul_endpoints [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) :
    (swap a b * p).SameCycle a b ↔ ¬ p.SameCycle a b := by
  classical
  let hit (j : ℕ) := (p ^ (j + 1)) a = a ∨ (p ^ (j + 1)) a = b
  have ex : ∃ j, hit j := by
    have pos := orderOf_pos p
    use orderOf p - 1
    left
    rw [show orderOf p - 1 + 1 = orderOf p by omega, pow_orderOf_eq_one, one_apply]
  let k := Nat.find ex
  have firstHit : hit k := Nat.find_spec ex
  have before (j : ℕ) (hj : j < k) : ¬ hit j := Nat.find_min ex hj
  let g := swap a b * p
  have walk (j : ℕ) (hj : j ≤ k) : (g ^ j) a = (p ^ j) a := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := before j (by omega)
      change ¬ (_ ∨ _) at h
      rw [pow_succ' g, mul_apply, ih (by omega), pow_succ' p, mul_apply]
      exact swap_apply_of_ne_of_ne (fun e => h (Or.inl (by simpa [pow_succ'] using e)))
        (fun e => h (Or.inr (by simpa [pow_succ'] using e)))
  have last : (g ^ (k + 1)) a = swap a b ((p ^ (k + 1)) a) := by
    rw [pow_succ' g, mul_apply, walk k le_rfl, pow_succ' p, mul_apply]
    rfl
  have avoid (j : ℕ) (hj : j < k + 1) : (p ^ j) a ≠ b := by
    cases j with
    | zero => simpa using hab
    | succ j => exact fun e => before j (by omega) (Or.inr e)
  rcases firstHit with ha | hb
  · have old := avoids_of_closed p a b k ha avoid
    have new : g.SameCycle a b := ⟨((k + 1 : ℕ) : ℤ), by
      rw [zpow_natCast, last, ha, swap_apply_left]⟩
    exact ⟨fun _ => old, fun _ => new⟩
  · have old : p.SameCycle a b := ⟨((k + 1 : ℕ) : ℤ), by rwa [zpow_natCast]⟩
    have new := avoids_of_closed g a b k (by rw [last, hb, swap_apply_right])
      (fun j hj => by rw [walk j (by omega)]; exact avoid j hj)
    exact ⟨fun h => (new h).elim, fun h => (h old).elim⟩

/-- Joining two orbits preserves all the old within-orbit connections. -/
theorem sameCycle_swap_mul_of_diff [Finite D] [DecidableEq D] (p : Perm D) {a b x y : D}
    (hd : ¬ p.SameCycle a b) (hxy : p.SameCycle x y) : (swap a b * p).SameCycle x y := by
  have hab : a ≠ b := fun e => hd (e.sameCycle p)
  have joined := (sameCycle_swap_mul_endpoints p hab).2 hd
  apply map_sameCycle p (swap a b * p) id _ hxy
  intro z
  have edge := (SameCycle.refl (swap a b * p) z).apply_right
  by_cases ha : p z = a
  · simpa [ha] using edge.trans (by simpa [ha] using joined.symm :
      (swap a b * p).SameCycle ((swap a b * p) z) a)
  by_cases hb : p z = b
  · simpa [hb] using edge.trans (by simpa [hb] using joined :
      (swap a b * p).SameCycle ((swap a b * p) z) b)
  simpa [swap_apply_of_ne_of_ne ha hb] using edge

private def orbitSet (p : Perm D) (x : D) : Set D := {y | p.SameCycle x y}

private theorem orbitSet_eq_iff (p : Perm D) {x y : D} :
    orbitSet p x = orbitSet p y ↔ p.SameCycle x y := by
  constructor
  · intro h
    have hy : y ∈ orbitSet p y := .refl _ _
    rwa [← h] at hy
  · intro h
    exact Set.ext fun _ => ⟨h.symm.trans, h.trans⟩

private noncomputable def faces [Finite D] (p : Perm D) : Finset (Set D) := by
  classical
  letI := Fintype.ofFinite D
  exact Finset.univ.image (orbitSet p)

private theorem mem_faces [Finite D] (p : Perm D) (S : Set D) :
    S ∈ faces p ↔ ∃ x, orbitSet p x = S := by classical simp [faces]

private theorem card_faces [Finite D] (p : Perm D) : (faces p).card = countCycles p := by
  classical
  let u (x : D) : ↥(faces p) := ⟨orbitSet p x, (mem_faces p _).2 ⟨x, rfl⟩⟩
  let v : Quotient (SameCycle.setoid p) → ↥(faces p) := Quotient.lift u
    (fun _ _ h => Subtype.ext ((orbitSet_eq_iff p).2 h))
  have inj : Function.Injective v := by
    intro x y
    induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
    intro h
    exact Quotient.sound ((orbitSet_eq_iff p).1 (congrArg Subtype.val h))
  have sur : Function.Surjective v := by
    intro S
    obtain ⟨x, hx⟩ := (mem_faces p _).1 S.property
    exact ⟨Quotient.mk _ x, Subtype.ext hx⟩
  simpa [countCycles] using (Nat.card_congr (Equiv.ofBijective v ⟨inj, sur⟩)).symm

private theorem orbitSet_away [Finite D] [DecidableEq D] (p : Perm D) (a b x : D)
    (ha : ¬ p.SameCycle x a) (hb : ¬ p.SameCycle x b) :
    orbitSet (swap a b * p) x = orbitSet p x := by
  let g := swap a b * p
  have walk (n : ℕ) : (g ^ n) x = (p ^ n) x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' g, mul_apply, ih, pow_succ' p, mul_apply]
      have here : p.SameCycle x (p ((p ^ n) x)) := (SameCycle.rfl.pow_right).apply_right
      exact swap_apply_of_ne_of_ne (fun h => ha (h ▸ here)) (fun h => hb (h ▸ here))
  ext y
  change g.SameCycle x y ↔ p.SameCycle x y
  constructor <;> intro h <;> obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  · rw [walk]; exact SameCycle.rfl.pow_right
  · rw [← walk]; exact SameCycle.rfl.pow_right

private noncomputable def away [Finite D] (p : Perm D) (a b : D) : Finset (Set D) := by
  classical exact (faces p).filter fun S => ¬ (a ∈ S ∨ b ∈ S)

private theorem away_subset [Finite D] [DecidableEq D] (p : Perm D) (a b : D) :
    away p a b ⊆ away (swap a b * p) a b := by
  classical
  intro S h
  obtain ⟨hS, hn⟩ := Finset.mem_filter.mp h
  obtain ⟨x, rfl⟩ := (mem_faces p S).1 hS
  apply Finset.mem_filter.mpr
  exact ⟨(mem_faces _ _).2 ⟨x, orbitSet_away _ _ _ _ (fun h => hn (.inl h))
    (fun h => hn (.inr h))⟩, hn⟩

private theorem away_eq [Finite D] [DecidableEq D] (p : Perm D) (a b : D) :
    away (swap a b * p) a b = away p a b := by
  apply Finset.Subset.antisymm _ (away_subset p a b)
  simpa [← mul_assoc] using away_subset (swap a b * p) a b

private theorem count_marked [Finite D] (p : Perm D) (a b : D) [Decidable (p.SameCycle a b)] :
    countCycles p = (if p.SameCycle a b then 1 else 2) + (away p a b).card := by
  classical
  have marked : ((faces p).filter fun S => a ∈ S ∨ b ∈ S) = {orbitSet p a, orbitSet p b} := by
    ext S
    simp only [Finset.mem_filter, mem_faces, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨x, rfl⟩, ha | hb⟩
      · exact .inl ((orbitSet_eq_iff p).2 ha)
      · exact .inr ((orbitSet_eq_iff p).2 hb)
    · rintro (rfl | rfl)
      · exact ⟨⟨a, rfl⟩, .inl SameCycle.rfl⟩
      · exact ⟨⟨b, rfl⟩, .inr SameCycle.rfl⟩
  have h := (faces p).card_filter_add_card_filter_not (fun S => a ∈ S ∨ b ∈ S)
  rw [marked, card_faces] at h
  change _ + (away p a b).card = countCycles p at h
  rw [← h]
  by_cases same : p.SameCycle a b
  · simp [same, (orbitSet_eq_iff p).2 same]
  · rw [ite_eq_right same, Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa using fun e => same ((orbitSet_eq_iff p).1 e)

/-- Cutting one face at two distinct landing darts splits it in two. -/
theorem countCycles_swap_mul_same [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) (hs : p.SameCycle a b) :
    countCycles (swap a b * p) = countCycles p + 1 := by
  classical
  rw [count_marked (swap a b * p) a b, count_marked p a b, away_eq]
  simp only [sameCycle_swap_mul_endpoints p hab, hs, not_true_eq_false, ↓reduceIte]
  omega

/-- Cutting different faces at their landing darts joins them into one face. -/
theorem countCycles_swap_mul_diff [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) (hd : ¬ p.SameCycle a b) :
    countCycles (swap a b * p) + 1 = countCycles p := by
  have h := countCycles_swap_mul_same (swap a b * p) hab ((sameCycle_swap_mul_endpoints p hab).2 hd)
  simpa [← mul_assoc] using h.symm

/-- Reversing every face walk leaves the face count unchanged. -/
theorem countCycles_inv (p : Perm D) : countCycles p⁻¹ = countCycles p := by
  unfold countCycles
  congr 2
  exact Setoid.ext fun _ _ => sameCycle_inv

/-- Transposing the two outgoing edges toggles connectivity of their source darts. -/
theorem sameCycle_mul_swap_endpoints [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) :
    (p * swap a b).SameCycle a b ↔ ¬ p.SameCycle a b := by
  rw [← sameCycle_inv (f := p * swap a b), mul_inv_rev, swap_inv,
    sameCycle_swap_mul_endpoints p⁻¹ hab, sameCycle_inv]

/-- All old within-face connections survive a merge at the source darts. -/
theorem sameCycle_mul_swap_of_diff [Finite D] [DecidableEq D] (p : Perm D) {a b x y : D}
    (hd : ¬ p.SameCycle a b) (hxy : p.SameCycle x y) : (p * swap a b).SameCycle x y := by
  rw [← sameCycle_inv, mul_inv_rev, swap_inv]
  exact sameCycle_swap_mul_of_diff p⁻¹ (by simpa using hd) hxy.inv

/-- Right multiplication by a transposition splitting a face increases the count by one. -/
theorem countCycles_mul_swap_same [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) (hs : p.SameCycle a b) :
    countCycles (p * swap a b) = countCycles p + 1 := by
  rw [← countCycles_inv (p * swap a b), mul_inv_rev, swap_inv,
    countCycles_swap_mul_same p⁻¹ hab hs.inv, countCycles_inv]

/-- Right multiplication by a transposition joining two faces decreases the count by one. -/
theorem countCycles_mul_swap_diff [Finite D] [DecidableEq D] (p : Perm D)
    {a b : D} (hab : a ≠ b) (hd : ¬ p.SameCycle a b) :
    countCycles (p * swap a b) + 1 = countCycles p := by
  rw [← countCycles_inv (p * swap a b), mul_inv_rev, swap_inv,
    countCycles_swap_mul_diff p⁻¹ hab (by simpa using hd), countCycles_inv]

/-- A common coarsening of the old orbits that identifies the cuts contains every new walk. -/
theorem sameCycle_mul_swap_le [Finite D] [DecidableEq D] (p : Perm D) (R : Setoid D)
    (hp : ∀ x y, p.SameCycle x y → R.r x y) {a b : D} (habR : R.r a b) :
    ∀ x y, (p * swap a b).SameCycle x y → R.r x y := by
  have edge (z : D) : R.r z ((p * swap a b) z) := by
    have s : R.r z (swap a b z) := by
      by_cases ha : z = a
      · simpa [ha] using habR
      by_cases hb : z = b
      · simpa [hb] using R.symm habR
      simp [swap_apply_of_ne_of_ne ha hb]
    exact R.trans s (hp _ _ SameCycle.rfl.apply_right)
  intro x y h
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply]; exact R.trans ih (edge _)

/-- A nonempty transitive dart permutation has exactly one face. -/
theorem countCycles_eq_one_of_forall [Nonempty D] (p : Perm D) (h : ∀ x y, p.SameCycle x y) :
    countCycles p = 1 := by
  let sub : Subsingleton (Quotient (SameCycle.setoid p)) :=
    ⟨fun x y => Quotient.inductionOn₂ x y (fun a b => Quotient.sound (h a b))⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨sub, Nonempty.map (Quotient.mk _) inferInstance⟩

end MultiGenus.Surgery
