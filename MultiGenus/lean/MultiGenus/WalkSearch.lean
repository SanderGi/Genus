/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Bounds

/-! # Breadth-first search for the shortest eligible return

Layer zero contains only the starting dart. Each new layer contains all darts
reachable in exactly one more turn. Testing starts at layer one, so a self-loop
counts as a return of length one. A shortest positive return repeats no dart
before its endpoint, hence the number of darts bounds the search depth.
-/

@[expose] public section

namespace MultiGenus.WalkSearch

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (step : D → D → Prop) [DecidableRel step]

/-- Darts reachable by one eligible turn from the current breadth-first layer. -/
def advance (s : Finset D) : Finset D :=
  Finset.univ.filter fun y => ∃ x ∈ s, step x y

omit [DecidableEq D] in
@[simp] theorem mem_advance {s : Finset D} {y : D} :
    y ∈ advance step s ↔ ∃ x ∈ s, step x y := by simp [advance]

/-- Search subsequent layers for the first visit to the target, up to the given depth. -/
def scan (target : D) (s : Finset D) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let t := advance step s
    if target ∈ t then some 1 else (scan target t fuel).map (· + 1)

/-- Length of the shortest positive return, or zero if the dart lies on no circuit. -/
def shortestReturn (d : D) : ℕ := (scan step d {d} (Fintype.card D)).getD 0

omit [DecidableEq D] in
/-- A layer contains exactly the endpoints of walks of its indicated length. -/
theorem mem_layer (n : ℕ) (s : Finset D) (y : D) :
    y ∈ (advance step)^[n] s ↔ ∃ p : ℕ → D, p 0 ∈ s ∧ p n = y ∧
      ∀ i < n, step (p i) (p (i + 1)) := by
  induction n generalizing s with
  | zero =>
    exact ⟨fun hy => ⟨fun _ => y, hy, rfl, by simp⟩, fun ⟨_, hm, e, _⟩ => e ▸ hm⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    constructor
    · rintro ⟨p, hp, he, hs⟩
      obtain ⟨x, hx, hxp⟩ := (mem_advance step).mp hp
      refine ⟨fun i => Nat.casesOn i x p, hx, he, ?_⟩
      rintro (_ | i) hi
      · exact hxp
      · exact hs i (by omega)
    · rintro ⟨p, hp, he, hs⟩
      exact ⟨fun i => p (i + 1), (mem_advance step).mpr ⟨p 0, hp, hs 0 (by omega)⟩,
        he, fun i hi => hs (i + 1) (by omega)⟩

private theorem scan_first (d : D) (s : Finset D) {fuel n : ℕ} (hn : 0 < n) (hf : n ≤ fuel)
    (hit : d ∈ (advance step)^[n] s)
    (first : ∀ j, 0 < j → j < n → d ∉ (advance step)^[j] s) :
    scan step d s fuel = some n := by
  induction fuel generalizing n s with
  | zero => omega
  | succ fuel ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => simp [scan, show d ∈ advance step s from hit]
      | succ k =>
        have miss := first 1 (by omega) (by omega)
        change d ∉ advance step s at miss
        rw [scan, ite_eq_right miss]
        rw [ih (advance step s) (by omega : 0 < k + 1) (by omega)
          (by simpa only [Function.iterate_succ_apply] using hit) (fun j hj hlt => ?_)]
        · rfl
        · exact first (j + 1) (by omega) (by omega)

private theorem scan_none (d : D) (s : Finset D) (fuel : ℕ)
    (miss : ∀ j, 0 < j → j ≤ fuel → d ∉ (advance step)^[j] s) :
    scan step d s fuel = none := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have h := miss 1 (by omega) (by omega)
    change d ∉ advance step s at h
    rw [scan, ite_eq_right h, ih]
    · rfl
    · exact fun j hj hj' => miss (j + 1) (by omega) (by omega)

omit [DecidableEq D] in
private theorem circuit_of_first {d : D} {n : ℕ} (hn : 0 < n)
    (hit : d ∈ (advance step)^[n] {d})
    (first : ∀ j, 0 < j → j < n → d ∉ (advance step)^[j] {d}) : Bounds.Circuit step d n := by
  obtain ⟨p, hstart, hend, hs⟩ := (mem_layer step n {d} d).mp hit
  have h0 := Finset.mem_singleton.mp hstart
  refine ⟨hn, p, h0, hend, ?_, hs⟩
  have no_repeat (i j : ℕ) (hij : i < j) (hj : j < n) (eq : p i = p j) : False := by
    let gap := j - i
    let m := n - gap
    have hgap : i + gap = j := by dsimp [gap]; omega
    have endIdx : m + gap = n := by dsimp [m, gap]; omega
    have hm : i < m := by dsimp [m, gap]; omega
    apply first m (by omega) (by dsimp [m, gap]; omega)
    apply (mem_layer step m {d} d).mpr
    refine ⟨fun t => if t ≤ i then p t else p (t + gap), by simpa using hstart,
      by simp [Nat.not_le.mpr hm, endIdx, hend], ?_⟩
    intro t ht
    rcases lt_trichotomy t i with h | rfl | h
    · simpa only [ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)] using hs t (by omega)
    · simpa only [ite_eq_left le_rfl, ite_eq_right (by omega : ¬ t + 1 ≤ t), eq,
        show t + 1 + gap = j + 1 by omega] using hs j hj
    · simpa only [ite_eq_right (Nat.not_le.mpr h), ite_eq_right (by omega : ¬ t + 1 ≤ i),
        show t + 1 + gap = t + gap + 1 by omega] using hs (t + gap) (by omega)
  intro i hi j hj eq
  rcases lt_trichotomy i j with lt | he | gt
  · exact (no_repeat i j lt hj eq).elim
  · exact he
  · exact (no_repeat j i gt hi eq.symm).elim

omit [DecidableEq D] in
private theorem hit_of_circuit {d : D} {n : ℕ} (hc : Bounds.Circuit step d n) :
    d ∈ (advance step)^[n] {d} := by
  obtain ⟨_, p, hp, he, _, hs⟩ := hc
  exact (mem_layer step n {d} d).mpr ⟨p, Finset.mem_singleton.mpr hp, he, hs⟩

omit [DecidableEq D] [DecidableRel step] in
private theorem circuit_le_card {d : D} {n : ℕ} (hc : Bounds.Circuit step d n) :
    n ≤ Fintype.card D := by
  obtain ⟨_, p, _, _, hi, _⟩ := hc
  simpa using Fintype.card_le_of_injective (fun i : Fin n => p i.val)
    (fun i j e => Fin.ext (hi i.isLt j.isLt e))

/-- The executable BFS computes the mathematical minimum over eligible dart-simple circuits. -/
theorem shortestReturn_eq_shortest (d : D) : shortestReturn step d = Bounds.shortest step d := by
  classical
  let hit (n : ℕ) := 0 < n ∧ d ∈ (advance step)^[n] {d}
  by_cases reaches : ∃ n, hit n
  · let n := Nat.find reaches
    obtain ⟨hn, hmem⟩ := Nat.find_spec reaches
    have first (j : ℕ) (pos : 0 < j) (lt : j < n) : d ∉ (advance step)^[j] {d} :=
      fun hm => Nat.find_min reaches lt ⟨pos, hm⟩
    have hc := circuit_of_first step hn hmem first
    have ex : ∃ k, Bounds.Circuit step d k := ⟨n, hc⟩
    rw [shortestReturn, scan_first step d {d} hn (circuit_le_card step hc) hmem first,
      Option.getD_some, Bounds.shortest, dite_eq_left ex]
    apply Nat.le_antisymm _ (Nat.find_min' ex hc)
    have hmin := Nat.find_spec ex
    exact Nat.find_min' reaches ⟨hmin.1, hit_of_circuit step hmin⟩
  · have noCircuit : ¬ ∃ n, Bounds.Circuit step d n :=
      fun ⟨n, hc⟩ => reaches ⟨n, hc.1, hit_of_circuit step hc⟩
    rw [shortestReturn, scan_none step d {d} _ (fun j hj _ hm => reaches ⟨j, hj, hm⟩),
      Bounds.shortest, dite_eq_right noCircuit]
    rfl

open Faces

/-- Eligible turns use only the row at the head. A reversal is allowed exactly when
all its outgoing darts have the same destination as the proposed successor. -/
def turn {rows : List (List ℕ)} (a b : Dart rows) : Prop :=
  b.val.1 = a.val.2 ∧ (b.val = a.val.swap ↔ ∀ w ∈ row rows b.val.1, w = b.val.2)

instance {rows : List (List ℕ)} : DecidableRel (turn (rows := rows)) :=
  fun a b => by unfold turn; infer_instance

/-- The local neighbor-list test agrees with the abstract dart eligibility relation. -/
theorem turn_iff {rows : List (List ℕ)} (h : Valid rows) (a b : Dart rows) :
    turn a b ↔ Bounds.rowStep h a b := by
  change (_ ∧ (_ ↔ _)) ↔ (_ ∧ (b = alpha h a ↔ _))
  have rev : b.val = a.val.swap ↔ b = alpha h a :=
    ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  apply and_congr_right
  intro _
  apply iff_congr rev
  constructor
  · intro onlyDest c hc
    change c.val.1 = b.val.1 at hc
    have hw := (mem_darts.mp c.prop).2
    rw [hc] at hw
    exact Subtype.ext (Prod.ext hc (onlyDest _ hw))
  · intro unique w hw
    let c : Dart rows := ⟨(b.val.1, w), mem_darts.mpr ⟨(mem_darts.mp b.prop).1, hw⟩⟩
    exact congrArg (fun d : Dart rows => d.val.2) (unique c rfl)

/-- Search the concrete directed graph of eligible turns, using just the rows and a dart. -/
def rowReturn {rows : List (List ℕ)} (d : Dart rows) : ℕ := shortestReturn turn d

/-- Computable local length for the reciprocal face bounds. -/
def rowLength {rows : List (List ℕ)} (_h : Valid rows) (d : Dart rows) : ℕ := rowReturn d

/-- The computed local lengths can be substituted directly into the bounds of Brinkmann. -/
theorem rowLength_eq {rows : List (List ℕ)} (h : Valid rows) (d : Dart rows) :
    rowLength h d = Bounds.shortest (Bounds.rowStep h) d := by
  change shortestReturn turn d = _
  rw [shortestReturn_eq_shortest]
  have eq : turn = Bounds.rowStep h := funext fun a => funext fun b => propext (turn_iff h a b)
  rw [eq]

/-- Sum the reciprocal BFS lengths, with one contribution per dart. -/
def fractionBound (rows : List (List ℕ)) : ℚ :=
  ∑ d : Dart rows, 1 / (rowReturn d : ℚ)

/-- The executable sum bounds the actual number of face orbits from above. -/
theorem orbitCount_le_fractionBound {rows : List (List ℕ)} (h : Valid rows) :
    (orbitCount rows : ℚ) ≤ fractionBound rows := by
  simpa only [fractionBound, ← rowLength_eq h, rowLength] using Bounds.orbitCount_le_shortest h

end MultiGenus.WalkSearch
