/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.SurgerySubdivide
public import MultiGenus.Genus

/-! # Leaf and degree-two reductions of dart rotations

A rotation is specified independently by its vertex orbits. Adding a dart to an
existing vertex inserts it into a cyclic slot. Removing the dart recovers both
the old permutation and the slot, so the arguments apply to every rotation.
-/

@[expose] public section

namespace MultiGenus.Reduction

open Equiv Equiv.Perm Surgery

variable {D V : Type*}

/-- The vertex rotations are precisely the cycles on the fibers of the origin map. -/
def Ordered (tail : D → V) (p : Perm D) : Prop :=
  ∀ x y, p.SameCycle x y ↔ tail x = tail y

/-- The Euler genus spectrum for a graph with a nonempty dart set. -/
def Attains (v e : Nat) (tail : D → V) (rev : Perm D) (g : Nat) : Prop :=
  ∃ p, Ordered tail p ∧ 2 + e = v + countCycles (p * rev) + 2 * g

/-- Give one extra dart the specified origin. -/
def atVertex (tail : D → V) (v : V) : Option D → V := fun x => x.elim v tail

private theorem option_same [Finite D] (p : Perm D) (x y : D) :
    SameCycle p.optionCongr (some x) (some y) ↔ p.SameCycle x y := by
  constructor
  · apply map_sameCycle p.optionCongr p (fun z => z.getD x)
    intro z
    cases z with
    | none => exact SameCycle.rfl
    | some z => exact SameCycle.rfl.apply_right
  · apply map_sameCycle p p.optionCongr some
    intro z
    exact SameCycle.rfl.apply_right

private theorem ordered_option [Finite D] (tail : D → V) (p : Perm D) :
    Ordered (Option.map tail) p.optionCongr ↔ Ordered tail p := by
  constructor
  · intro h x y
    simpa only [option_same, Option.map_some, Option.some.injEq] using h (some x) (some y)
  · intro h x y
    cases x <;> cases y
    · exact ⟨fun _ => rfl, fun _ => SameCycle.rfl⟩
    · exact ⟨(fun hs => by cases hs.eq_of_left rfl), fun h => by cases h⟩
    · exact ⟨(fun hs => by cases hs.eq_of_right rfl), fun h => by cases h⟩
    · simpa only [option_same, Option.map_some, Option.some.injEq] using h _ _

private theorem fresh_iff [Finite D] (tail : D → V) (q : Perm (Option D)) :
    Ordered (Option.map tail) q ↔ ∃ p, Ordered tail p ∧ q = p.optionCongr := by
  classical
  constructor
  · intro h
    have fixed : q none = none := by
      have eq := (h none (q none)).mp SameCycle.rfl.apply_right
      cases he : q none with
      | none => rfl
      | some z => simp [he] at eq
    have eq : (removeNone q).optionCongr = q := by rw [map_equiv_removeNone, fixed, swap_self]; rfl
    exact ⟨_, (ordered_option ..).mp (eq.symm ▸ h), eq.symm⟩
  · rintro ⟨p, h, rfl⟩
    exact (ordered_option ..).mpr h

private theorem splice_same [Finite D] [DecidableEq D] (p : Perm D) (a : D) (x y : Option D) :
    (subdivideBefore p a).SameCycle x y ↔ p.SameCycle (x.getD a) (y.getD a) := by
  let q := subdivideBefore p a
  have project (z : Option D) : p.SameCycle (z.getD a) ((q z).getD a) := by
    cases z with
    | none => simpa [q] using SameCycle.refl p a
    | some z =>
      simp only [q, subdivideBefore_some, Option.getD_some]
      split <;> rename_i h
      · exact h ▸ (SameCycle.refl p z).apply_right
      · exact SameCycle.rfl.apply_right
  have lift (x y : D) (h : p.SameCycle x y) : q.SameCycle (some x) (some y) := by
    apply sameCycle_swap_mul_of_diff p.optionCongr _ ((option_same ..).mpr h)
    intro hn
    cases hn.eq_of_left rfl
  have retract (z : Option D) : q.SameCycle z (some (z.getD a)) := by
    cases z with
    | some => exact SameCycle.rfl
    | none => simpa [q] using (SameCycle.refl q none).apply_right
  exact ⟨map_sameCycle q p (fun z => z.getD a) project,
    fun h => (retract x).trans ((lift _ _ h).trans (retract y).symm)⟩

private theorem slot_iff [Finite D] [DecidableEq D] (tail : D → V) (a : D)
    (q : Perm (Option D)) :
    Ordered (atVertex tail (tail a)) q ↔
      ∃ p k, Ordered tail p ∧ tail k = tail a ∧ q = subdivideBefore p k := by
  constructor
  · intro h
    have same := (h none (some a)).mpr rfl
    have nf : q none ≠ none := fun e => by cases same.eq_of_left e
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr nf)
    have eq : subdivideBefore (removeNone q) k = q := by
      rw [subdivideBefore, map_equiv_removeNone, hk, ← mul_assoc, swap_mul_self, one_mul]
    refine ⟨_, k, ?_, ?_, eq.symm⟩
    · intro x y
      have H := h (some x) (some y)
      rw [← eq] at H
      exact (splice_same _ k (some x) (some y)).symm.trans H
    · exact ((h none (some k)).mp (hk ▸ (SameCycle.refl q none).apply_right)).symm
  · rintro ⟨p, k, hp, hk, rfl⟩ x y
    rw [splice_same, hp]
    cases x <;> cases y <;> simp [atVertex, hk]

/-- The inner and outer `none` denote the two new darts. -/
abbrev Added (D : Type*) := Option (Option D)

/-- Act on old darts by `p` and transpose the two new darts. -/
def pairPerm [DecidableEq D] (p : Perm D) : Perm (Added D) :=
  subdivideBefore p.optionCongr none

private theorem pair_old [DecidableEq D] (p : Perm D) (d : D) :
    pairPerm p (some (some d)) = some (some (p d)) := by
  simp [pairPerm, subdivideBefore_some]

private theorem pair_inner [DecidableEq D] (p : Perm D) :
    pairPerm p (some none) = none := by simp [pairPerm, subdivideBefore_some]

private theorem pair_outer [DecidableEq D] (p : Perm D) :
    pairPerm p none = some none := subdivideBefore_none ..

/-- The inner dart joins the old attachment vertex and the outer dart is the new leaf. -/
def leafTail (tail : D → V) (atV : V) : Added D → Option V := Option.map (atVertex tail atV)

/-- Place the leaf edge immediately before the chosen dart of its attachment vertex. -/
def leafRotation [DecidableEq D] (p : Perm D) (k : D) : Perm (Added D) :=
  (subdivideBefore p k).optionCongr

private theorem leaf_ordered [Finite D] [DecidableEq D] (tail : D → V) (a : D)
    (q : Perm (Added D)) :
    Ordered (leafTail tail (tail a)) q ↔
      ∃ p k, Ordered tail p ∧ tail k = tail a ∧ q = leafRotation p k := by
  rw [leafTail, fresh_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (slot_iff tail a r).mp hr
    exact ⟨p, k, hp, hk, rfl⟩
  · rintro ⟨p, k, hp, hk, rfl⟩
    exact ⟨_, (slot_iff tail a _).mpr ⟨p, k, hp, hk, rfl⟩, rfl⟩

/-- A facial walk detours to the leaf and back before reaching its old target. -/
theorem leaf_face [DecidableEq D] (p rev : Perm D) (k : D) :
    leafRotation p k * pairPerm rev =
      subdivideBefore (subdivideBefore (p * rev) k) (some k) := by
  ext (d | d)
  · simp [Perm.mul_apply, pair_outer, leafRotation]
  cases d with
  | none => simp [Perm.mul_apply, pair_inner, leafRotation, subdivideBefore_some]
  | some d =>
    by_cases h : p (rev d) = k <;>
      simp [Perm.mul_apply, pair_old, leafRotation, subdivideBefore_some, h]

/-- Adding or deleting a leaf at an incident vertex preserves the entire attainable spectrum. -/
theorem leaf_attains_iff [Finite D] [DecidableEq D] (v e : Nat) (tail : D → V)
    (rev : Perm D) (a : D) (g : Nat) :
    Attains (v + 1) (e + 1) (leafTail tail (tail a)) (pairPerm rev) g ↔ Attains v e tail rev g := by
  have eq (p : Perm D) (k : D) :
      countCycles (leafRotation p k * pairPerm rev) = countCycles (p * rev) := by
    rw [leaf_face, countCycles_subdivideBefore, countCycles_subdivideBefore]
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨p, k, hp, _, rfl⟩ := (leaf_ordered tail a q).mp hq
    exact ⟨p, hp, by rw [eq] at he; omega⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨_, (leaf_ordered tail a _).mpr ⟨p, a, hp, rfl, rfl⟩, by rw [eq]; omega⟩

/-- Both new darts originate at the new degree-two vertex. -/
def subdivTail (tail : D → V) : Added D → Option V := atVertex (Option.map tail) none

private theorem subdiv_ordered [Finite D] [DecidableEq D] (tail : D → V) (q : Perm (Added D)) :
    Ordered (subdivTail tail) q ↔ ∃ p, Ordered tail p ∧ q = pairPerm p := by
  change Ordered (atVertex (Option.map tail) (Option.map tail none)) q ↔ _
  rw [slot_iff]
  constructor
  · rintro ⟨r, k, hr, hk, rfl⟩
    have : k = none := by cases k <;> simp_all
    subst k
    obtain ⟨p, hp, rfl⟩ := (fresh_iff tail r).mp hr
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, none, (ordered_option ..).mpr hp, rfl, rfl⟩

/-- Replace the old reverse pair `a ↔ b` by two reverse pairs.
Conjugating by the displayed exchange sends the old pairs to `a ↔ inner` and `b ↔ outer`. -/
def subdivReverse [DecidableEq D] (rev : Perm D) (b : D) : Perm (Added D) :=
  let s := swap (some (some b)) (some none)
  s * pairPerm rev * s

/-- In each traversal of the subdivided edge the new degree-two rotation contributes one
extra facial step. The two subdivided steps can belong to the same face. -/
theorem subdiv_face [DecidableEq D] (p rev : Perm D) {a b : D}
    (ab : a ≠ b) (ha : rev a = b) (hb : rev b = a) :
    pairPerm p * subdivReverse rev b =
      subdivideBefore (subdivideBefore (p * rev) (p a)) (some (p b)) := by
  ext z
  cases z with
  | none =>
    simp [Perm.mul_apply, subdivReverse, pair_outer, swap_apply_def, pair_old]
  | some z =>
    cases z with
    | none =>
      simp [Perm.mul_apply, subdivReverse, pair_old, swap_apply_def,
        hb, ab, subdivideBefore_some]
    | some x =>
      by_cases hx : x = b
      · subst x
        simp [Perm.mul_apply, subdivReverse, pair_inner, pair_outer, swap_apply_def,
          hb, subdivideBefore_some]
      by_cases hy : x = a
      · subst x
        simp [Perm.mul_apply, subdivReverse, pair_old, pair_inner, swap_apply_def,
          ha, ab, ab.symm, subdivideBefore_some]
      have na : rev x ≠ a := fun h => hx (rev.injective (h.trans hb.symm))
      have nb : rev x ≠ b := fun h => hy (rev.injective (h.trans ha.symm))
      simp [Perm.mul_apply, subdivReverse, pair_old, swap_apply_def, hx, na, nb,
        subdivideBefore_some]

/-- Subdividing an edge and suppressing the resulting degree-two vertex preserve every genus. -/
theorem subdiv_attains_iff [Finite D] [DecidableEq D] (v e : Nat) (tail : D → V)
    (rev : Perm D) {a b : D} (ab : a ≠ b) (ha : rev a = b) (hb : rev b = a) (g : Nat) :
    Attains (v + 1) (e + 1) (subdivTail tail) (subdivReverse rev b) g ↔
      Attains v e tail rev g := by
  have eq (p : Perm D) :
      countCycles (pairPerm p * subdivReverse rev b) = countCycles (p * rev) := by
    rw [subdiv_face p rev ab ha hb, countCycles_subdivideBefore, countCycles_subdivideBefore]
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨p, hp, rfl⟩ := (subdiv_ordered tail q).mp hq
    exact ⟨p, hp, by rw [eq] at he; omega⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨_, (subdiv_ordered tail _).mpr ⟨p, hp, rfl⟩, by rw [eq]; omega⟩

/-- Give the two new darts the origins of the ends of an existing edge. -/
def parallelTail (tail : D → V) (u v : V) : Added D → V := atVertex (atVertex tail u) v

/-- Choose a slot before `x` and a slot before `y` at the respective vertices. -/
def parallelRotation [DecidableEq D] (p : Perm D) (x y : D) : Perm (Added D) :=
  subdivideBefore (subdivideBefore p x) (some y)

private theorem parallel_ordered [Finite D] [DecidableEq D] (tail : D → V) (a b : D)
    (ne : tail a ≠ tail b) (q : Perm (Added D)) :
    Ordered (parallelTail tail (tail a) (tail b)) q ↔
      ∃ p x y, Ordered tail p ∧ tail x = tail a ∧ tail y = tail b ∧ q = parallelRotation p x y := by
  change Ordered (atVertex (atVertex tail (tail a)) (atVertex tail (tail a) (some b))) q ↔ _
  rw [slot_iff]
  constructor
  · rintro ⟨r, k, hr, hk, rfl⟩
    obtain ⟨p, x, hp, hx, rfl⟩ := (slot_iff tail a r).mp hr
    cases k with
    | none => exact (ne hk).elim
    | some y => exact ⟨p, x, y, hp, hx, hk, rfl⟩
  · rintro ⟨p, x, y, hp, hx, hy, rfl⟩
    exact ⟨_, some y, (slot_iff tail a _).mpr ⟨p, x, hp, hx, rfl⟩, hy, rfl⟩

/-- Compressing the new facial steps for a parallel edge exchanges its two landing darts. -/
theorem parallel_face [DecidableEq D] (p rev : Perm D) {x y : D} (ne : x ≠ y) :
    parallelRotation p x y * pairPerm rev =
      subdivideBefore (subdivideBefore (swap x y * (p * rev)) y) (some x) := by
  ext z
  cases z with
  | none => simp [Perm.mul_apply, pair_outer, parallelRotation, subdivideBefore_some, ne]
  | some z =>
    cases z with
    | none => simp [Perm.mul_apply, pair_inner, parallelRotation, subdivideBefore_some, ne.symm]
    | some z =>
      by_cases hx : p (rev z) = x
      · simp [Perm.mul_apply, pair_old, parallelRotation, subdivideBefore_some, hx]
      by_cases hy : p (rev z) = y
      · simp [Perm.mul_apply, pair_old, parallelRotation, subdivideBefore_some, hy, ne, ne.symm]
      simp [Perm.mul_apply, pair_old, parallelRotation, subdivideBefore_some, hx, hy,
        swap_apply_of_ne_of_ne hx hy]

private theorem parallel_count [Finite D] [DecidableEq D] (p rev : Perm D) {x y : D} (ne : x ≠ y) :
    countCycles (parallelRotation p x y * pairPerm rev) = countCycles (swap x y * (p * rev)) := by
  rw [parallel_face p rev ne, countCycles_subdivideBefore, countCycles_subdivideBefore]

/-- Every chosen rotation has an exact nonnegative Euler genus. This is supplied by connectedness
in applications, and allows the minimum comparison to use natural numbers throughout. -/
def EulerExact (v e : Nat) (tail : D → V) (rev : Perm D) : Prop :=
  ∀ p, Ordered tail p → ∃ g : Nat, 2 + e = v + countCycles (p * rev) + 2 * g

/-- A parallel edge can be inserted without increasing genus by following the face of the
existing edge `a`. Deleting an arbitrarily placed parallel edge can only lower the genus. -/
theorem parallel_atMost_iff [Finite D] [DecidableEq D] (v e : Nat) (tail : D → V)
    (rev : Perm D) (a : D) (ne : tail a ≠ tail (rev a))
    (exactEuler : EulerExact v e tail rev) (target : Nat) :
    (∃ g ≤ target, Attains v (e + 1) (parallelTail tail (tail a) (tail (rev a))) (pairPerm rev) g) ↔
      ∃ g ≤ target, Attains v e tail rev g := by
  constructor
  · rintro ⟨g, hg, q, hq, eq⟩
    obtain ⟨p, x, y, hp, hx, hy, rfl⟩ := (parallel_ordered tail a (rev a) ne q).mp hq
    obtain ⟨g₀, he⟩ := exactEuler p hp
    have hxy : x ≠ y := fun h => ne (hx.symm.trans ((congrArg tail h).trans hy))
    rw [parallel_count p rev hxy] at eq
    refine ⟨g₀, ?_, p, hp, he⟩
    by_cases hs : (p * rev).SameCycle x y
    · have := countCycles_swap_mul_same (p * rev) hxy hs
      omega
    · have := countCycles_swap_mul_diff (p * rev) hxy hs
      omega
  · rintro ⟨g, hg, p, hp, he⟩
    let y := p (rev a)
    have hy : tail y = tail (rev a) := ((hp (rev a) y).mp SameCycle.rfl.apply_right).symm
    have hxy : a ≠ y := fun h => ne ((congrArg tail h).trans hy)
    have hs : (p * rev).SameCycle a y := SameCycle.rfl.apply_right
    refine ⟨g, hg, _, (parallel_ordered tail a (rev a) ne _).mpr ⟨p, a, y, hp, rfl, hy, rfl⟩, ?_⟩
    rw [parallel_count p rev hxy, countCycles_swap_mul_same _ hxy hs]
    omega

/-- The graph with a length-two path parallel to an existing edge has one extra vertex and
two extra edges. Its new path is the subdivision of the added parallel edge. -/
def triangleTail (tail : D → V) (u v : V) := subdivTail (parallelTail tail u v)

/-- Reversal pairs the two halves of the added parallel path through its internal vertex. -/
def triangleReverse [DecidableEq D] (rev : Perm D) : Perm (Added (Added D)) :=
  subdivReverse (pairPerm rev) (some none)

/-- Suppressing a degree-two vertex whose neighbors are already adjacent preserves every
upper-bound decision for genus, and hence the minimum attainable genus. -/
theorem triangle_atMost_iff [Finite D] [DecidableEq D] (v e : Nat) (tail : D → V)
    (rev : Perm D) (a : D) (ne : tail a ≠ tail (rev a))
    (exactEuler : EulerExact v e tail rev) (target : Nat) :
    (∃ g ≤ target, Attains (v + 1) (e + 2) (triangleTail tail (tail a) (tail (rev a)))
        (triangleReverse rev) g) ↔ ∃ g ≤ target, Attains v e tail rev g := by
  rw [← parallel_atMost_iff v e tail rev a ne exactEuler target]
  apply exists_congr
  intro g
  apply and_congr_right
  intro _
  exact subdiv_attains_iff v (e + 1) _ (pairPerm rev) (a := none) (b := some none)
    (by simp) (pair_outer rev) (pair_inner rev) g

private theorem least_of_threshold {P Q : Set Nat} {g : Nat}
    (le : ∀ k, (∃ h ≤ k, h ∈ P) ↔ ∃ h ≤ k, h ∈ Q) (hg : IsLeast P g) : IsLeast Q g := by
  have bound {h} (hh : h ∈ Q) : g ≤ h := by
    obtain ⟨i, ih, hi⟩ := (le h).mpr ⟨h, le_rfl, hh⟩
    exact (hg.2 hi).trans ih
  obtain ⟨i, ig, hi⟩ := (le g).mp ⟨g, le_rfl, hg.1⟩
  exact ⟨le_antisymm ig (bound hi) ▸ hi, fun _ => bound⟩

/-- The old and reduced spectra have exactly the same least element. -/
theorem triangle_minimum_iff [Finite D] [DecidableEq D] (v e : Nat) (tail : D → V)
    (rev : Perm D) (a : D) (ne : tail a ≠ tail (rev a))
    (exactEuler : EulerExact v e tail rev) (g : Nat) :
    IsLeast {h | Attains (v + 1) (e + 2) (triangleTail tail (tail a) (tail (rev a)))
        (triangleReverse rev) h} g ↔ IsLeast {h | Attains v e tail rev h} g := by
  have eq := triangle_atMost_iff v e tail rev a ne exactEuler
  exact ⟨least_of_threshold eq, least_of_threshold (fun k => (eq k).symm)⟩

open Faces Rotations

/-- On the actual darts of a connected simple input every vertex ordering has an exact
nonnegative Euler genus, including orderings other than the displayed input rows. -/
theorem eulerExact_darts {n : Nat} {edges : List Edge} {rows : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (h : Legal n edges rows)
    (hn : 1 < n) :
    EulerExact n edges.length (fun x : Dart rows => x.val.1) (alpha (valid_of_legal G h)) := by
  let _ : Nonempty (Dart rows) :=
    ⟨(Map.origin_surjective h con hn (⟨0, con.1⟩ : Fin n)).choose⟩
  intro p hp
  have orbit (x y : Dart rows) : p.SameCycle x y ↔ (rho rows).SameCycle x y :=
    (hp x y).trans (rho_sameCycle_iff (valid_of_legal G h) x y).symm
  obtain ⟨g, he⟩ := Euler.exists_genus p (Map.pairs G h) (Map.pairs_distinct G h)
    (fun q href => Map.connected G h con q (fun x y same => href x y ((orbit x y).mpr same)))
  have vc : countCycles p = n := by
    rw [countCycles, show SameCycle.setoid p = SameCycle.setoid (rho rows) from Setoid.ext orbit]
    exact Map.vertex_cycles G h con hn
  have fold (ps : List (Dart rows × Dart rows)) (r : Perm (Dart rows)) :
      ps.foldl (fun f e => f * swap e.1 e.2) r = r * (ps.map (fun e => swap e.1 e.2)).prod := by
    induction ps generalizing r with
    | nil => simp
    | cons e es ih => simp [ih, mul_assoc]
  have product := Map.fold_pairs G h
  rw [fold] at product
  change _ = rho rows * alpha (valid_of_legal G h) at product
  rw [vc, fold, mul_left_cancel product] at he
  exact ⟨g, by simpa [Map.pairs] using he⟩

/-- Each legal row witness on a connected graph of order at least two gives a dart
rotation with exactly the genus computed by the search. -/
theorem attains_genusOf {n : Nat} {edges : List Edge} {rows : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (h : Legal n edges rows)
    (hn : 1 < n) : Attains n edges.length (fun x : Dart rows => x.val.1)
      (alpha (valid_of_legal G h)) (genusOf n edges.length rows) := by
  refine ⟨rho rows, rho_sameCycle_iff (valid_of_legal G h), ?_⟩
  have many : rows ≠ [[]] := by intro eq; have := h.1; simp_all
  have hf := faceCount_eq (valid_of_legal G h)
  simp only [many, ite_false] at hf
  rw [← show faceCount rows = countCycles (rho rows * alpha (valid_of_legal G h)) from hf]
  exact euler_genus G con h

/-- The isolated-vertex base case has a single empty row. Adding its first leaf produces
the unique rotation of a single edge, also of genus zero. -/
theorem isolated_leaf_iff (g : Nat) : Realizes 2 [(0, 1)] g ↔ Realizes 1 [] g := by
  have one (rs : Rows) : Legal 1 [] rs ↔ rs = [[]] := by
    rw [← mem_enumerate_iff]
    exact List.mem_singleton
  have two (rs : Rows) : Legal 2 [(0, 1)] rs ↔ rs = [[1], [0]] := by
    rw [← mem_enumerate_iff]
    exact List.mem_singleton
  have f1 : faceCount [[]] = 1 := by decide
  have f2 : faceCount [[1], [0]] = 1 := by decide
  simp only [Realizes, one, two, exists_eq_left, f1, f2, List.length_cons, List.length_nil]
  omega

/-- The diamond graph has a one-face genus-one rotation, while deleting its degree-two
vertex 3 leaves a triangle, all of whose rotations have two faces and genus zero. -/
theorem triangle_spectrum_changes :
    Realizes 4 [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3)] 1 ∧
      ¬ Realizes 3 [(0, 1), (0, 2), (1, 2)] 1 := by
  constructor
  · refine ⟨[[1, 2, 3], [0, 2, 3], [0, 1], [0, 1]], (mem_enumerate_iff ..).mp ?_, ?_⟩
    all_goals decide
  · rintro ⟨rs, hr, he⟩
    have allTwo : (enumerate 3 [(0, 1), (0, 2), (1, 2)]).all (fun r => faceCount r == 2) :=
      by decide
    have two := List.all_eq_true.mp allTwo rs ((mem_enumerate_iff ..).mpr hr)
    simp only [beq_iff_eq] at two
    simp [two] at he

end MultiGenus.Reduction
