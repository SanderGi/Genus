/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Faces
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Facial walks and the lower genus bounds of Brinkmann

Each orbit of the face permutation contributes exactly one to the sum of reciprocal lengths
over all darts. The eligible walks used for the bound depend only on the graph.
-/

@[expose] public section

namespace MultiGenus.Bounds

open Finset Equiv

variable {D V : Type*} [Fintype D]

/-- A legal turn in the dart graph. A dart may reverse at its head exactly when it is a leaf. -/
def Eligible (tail : D → V) (rev : D → D) (d e : D) : Prop :=
  tail e = tail (rev d) ∧ (e = rev d ↔ ∀ a, tail a = tail e → a = e)

/-- An eligible circuit of length `n`, starting on `d`. Distinctness is on directed edges. -/
def Circuit (step : D → D → Prop) (d : D) (n : ℕ) : Prop :=
  0 < n ∧ ∃ p : ℕ → D, p 0 = d ∧ p n = d ∧
    Set.InjOn p (Set.Iio n) ∧ ∀ i < n, step (p i) (p (i + 1))

/-- Minimum eligible circuit length through a dart. Zero denotes an empty set of circuits. -/
noncomputable def shortest (step : D → D → Prop) (d : D) : ℕ := by
  classical
  exact if h : ∃ n, Circuit step d n then Nat.find h else 0

/-- Darts of the face containing `d`, including singleton faces. -/
noncomputable def face (f : Perm D) (d : D) : Finset D := by
  classical exact univ.filter (f.SameCycle d)

private theorem mem_face (f : Perm D) (d : D) : d ∈ face f d := by
  classical simp [face, Perm.SameCycle.rfl]

private theorem face_eq {f : Perm D} {d e : D} (h : f.SameCycle d e) : face f d = face f e := by
  classical
  ext x
  simpa [face] using (show f.SameCycle d x ↔ f.SameCycle e x from
    ⟨h.symm.trans, h.trans⟩)

private theorem face_cycle (f : Perm D) (d : D) : f.IsCycleOn (face f d) := by
  classical
  refine ⟨f.bijOn (fun x => ?_), fun _ hx _ hy => ?_⟩
  · simp [face]
  · simp only [face, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    exact hx.symm.trans hy

/-- Traversing one face supplies a circuit witness, also at vertices of degree one. -/
theorem face_circuit (f : Perm D) {step : D → D → Prop} (hstep : ∀ d, step d (f d)) (d : D) :
    Circuit step d (face f d).card := by
  have h := face_cycle f d
  have hd := mem_face f d
  refine ⟨card_pos.mpr ⟨_, hd⟩, fun i => (f ^ i) d, rfl, h.pow_card_apply hd,
    h.injOn_pow_apply hd, fun i _ => ?_⟩
  simpa only [pow_succ', Perm.mul_apply] using hstep ((f ^ i) d)

/-- The shortest eligible circuit is positive and bounded by the actual face length. -/
theorem shortest_le_face (f : Perm D) {step : D → D → Prop} (hstep : ∀ d, step d (f d)) (d : D) :
    0 < shortest step d ∧ shortest step d ≤ (face f d).card := by
  classical
  have h := face_circuit f hstep d
  have ex : ∃ n, Circuit step d n := ⟨_, h⟩
  simpa [shortest, ex] using And.intro (Nat.find_spec ex).1 (Nat.find_min' ex h)

/-- Count the actual faces by charging each dart the reciprocal of its face length. -/
theorem face_count_eq_sum (f : Perm D) :
    (Nat.card (Quotient (Perm.SameCycle.setoid f)) : ℚ) =
      ∑ d, 1 / ((face f d).card : ℚ) := by
  classical
  let F := Quotient (Perm.SameCycle.setoid f)
  let : Fintype F := Fintype.ofFinite _
  let q : D → F := Quotient.mk _
  rw [← univ.sum_fiberwise q]
  change (Nat.card F : ℚ) = _
  have each (c : F) : ∑ d ∈ univ.filter (fun d => q d = c), 1 / ((face f d).card : ℚ) = 1 := by
    induction c using Quotient.inductionOn with
    | _ d =>
      have hf : univ.filter (fun e => q e = q d) = face f d := by
        ext e
        simp only [face, mem_filter, mem_univ, true_and]
        exact ⟨fun h => (show f.SameCycle e d from Quotient.exact h).symm,
          fun h => Quotient.sound h.symm⟩
      rw [hf]
      calc
        _ = ∑ _e ∈ face f d, 1 / ((face f d).card : ℚ) := by
          refine sum_congr rfl (fun e he => ?_)
          have h : f.SameCycle d e := by simpa [face] using he
          rw [face_eq h]
        _ = 1 := by
          have hn : ((face f d).card : ℚ) ≠ 0 := by
            exact_mod_cast (card_pos.mpr ⟨_, mem_face f d⟩).ne'
          simp [nsmul_eq_mul, hn]
  simp only [each, sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- The first fractional bound before the maximum-length multiplicity improvement. -/
theorem face_count_le_shortest (f : Perm D) {step : D → D → Prop} (hstep : ∀ d, step d (f d)) :
    (Nat.card (Quotient (Perm.SameCycle.setoid f)) : ℚ) ≤
      ∑ d, 1 / (shortest step d : ℚ) := by
  rw [face_count_eq_sum]
  refine sum_le_sum fun d _ => ?_
  obtain ⟨hp, hle⟩ := shortest_le_face f hstep d
  exact one_div_le_one_div_of_le (by exact_mod_cast hp) (by exact_mod_cast hle)

/-- Sound integer pruning from a certified rational upper face bound and Euler's identity. -/
theorem prune_of_face_bound {v e faces genus target : ℕ} {upper : ℚ}
    (euler : 2 * genus + v + faces = 2 + e) (bound : (faces : ℚ) ≤ upper)
    (prune : 2 * target + v + ⌊upper⌋ < 2 + (e : ℤ)) : target < genus := by
  have h : (faces : ℤ) ≤ ⌊upper⌋ := Int.le_floor.mpr (by exact_mod_cast bound)
  have he : 2 * (genus : ℤ) + v + faces = 2 + e := by exact_mod_cast euler
  exact_mod_cast (show (target : ℤ) < genus by linarith)


omit [Fintype D] in
private theorem smallest_sum_le (w : D → ℚ) {t q : Finset D}
    (hc : t.card = q.card) (hs : ∀ i ∈ t, ∀ j ∉ t, w i ≤ w j) :
    ∑ i ∈ t, w i ≤ ∑ i ∈ q, w i := by
  classical
  let b := (t \ q).equivOfCardEq (card_sdiff_comm hc)
  have hdiff : ∑ i ∈ t \ q, w i ≤ ∑ i ∈ q \ t, w i := by
    rw [← sum_coe_sort (t \ q) w, ← sum_coe_sort (q \ t) w]
    calc
      _ ≤ ∑ i : ↥(t \ q), w (b i) := sum_le_sum fun i _ =>
        hs _ (mem_sdiff.mp i.prop).1 _ (mem_sdiff.mp (b i).prop).2
      _ = _ := b.sum_comp (fun i => w i.val)
  have ht := sum_sdiff (inter_subset_left : t ∩ q ⊆ t) (f := w)
  have hq := sum_sdiff (inter_subset_right : t ∩ q ⊆ q) (f := w)
  have ht' : t \ (t ∩ q) = t \ q := by ext; simp
  have hq' : q \ (t ∩ q) = q \ t := by ext; simp
  rw [ht'] at ht
  rw [hq'] at hq
  linarith

/-- Brinkmann's first strengthened face bound. If `m` is attained as a local length bound,
the largest `m` entries can all be raised to `m`. Ties in the choice of `top` are immaterial. -/
theorem face_count_le_top [DecidableEq D] (f : Perm D) (k : D → ℕ) (d : D) (top : Finset D)
    (hpos : ∀ i, 0 < k i) (hface : ∀ i, k i ≤ (face f i).card)
    (hcard : top.card = k d) (horder : ∀ i ∈ top, ∀ j ∉ top, k j ≤ k i) :
    (Nat.card (Quotient (Perm.SameCycle.setoid f)) : ℚ) ≤
      (∑ _i ∈ top, 1 / (k d : ℚ)) + ∑ i ∈ topᶜ, 1 / (k i : ℚ) := by
  classical
  obtain ⟨q, hsub, hq⟩ := exists_subset_card_eq (hface d)
  let w (i : D) : ℚ := 1 / (k i : ℚ)
  let a (i : D) : ℚ := 1 / ((face f i).card : ℚ)
  have hcomp : ∑ i ∈ qᶜ, w i ≤ ∑ i ∈ topᶜ, w i := by
    have h := smallest_sum_le w (hcard.trans hq.symm) fun i hi j hj =>
      one_div_le_one_div_of_le (by exact_mod_cast hpos j) (by exact_mod_cast horder i hi j hj)
    linarith [sum_add_sum_compl q w, sum_add_sum_compl top w]
  rw [face_count_eq_sum]
  change ∑ i, a i ≤ _
  rw [← sum_add_sum_compl q a]
  apply add_le_add
  · have h : ∑ i ∈ q, a i ≤ ∑ _i ∈ q, 1 / (k d : ℚ) := by
      apply sum_le_sum
      intro i hi
      have hdi : f.SameCycle d i := by simpa [face] using hsub hi
      dsimp [a]
      rw [← face_eq hdi]
      exact one_div_le_one_div_of_le (by exact_mod_cast hpos d) (by exact_mod_cast hface d)
    simpa only [sum_const, hq, hcard] using h
  · refine le_trans (sum_le_sum fun i _ => ?_) hcomp
    exact one_div_le_one_div_of_le (by exact_mod_cast hpos i) (by exact_mod_cast hface i)

/-- Scaled dart weight, rounded up using only natural-number arithmetic. -/
def faceWeight (scale k : ℕ) : ℕ := (scale + k - 1) / k

/-- Each integer dart weight is a conservative approximation after division by its scale. -/
theorem le_faceWeight {scale k : ℕ} (hs : 0 < scale) (hk : 0 < k) :
    1 / (k : ℚ) ≤ (faceWeight scale k : ℚ) / scale := by
  rw [le_div_iff₀ (by exact_mod_cast hs), one_div_mul_eq_div, div_le_iff₀ (by exact_mod_cast hk)]
  have h := Nat.mod_lt (scale + k - 1) hk
  have e := Nat.mod_add_div (scale + k - 1) k
  have hn : scale ≤ faceWeight scale k * k := by
    rw [Nat.mul_comm]
    unfold faceWeight
    omega
  exact_mod_cast hn

/-- Sum of scaled, upward-rounded reciprocal contributions. -/
def scaledSum (scale : ℕ) (k : D → ℕ) : ℕ := ∑ d, faceWeight scale (k d)

/-- Rounding up each reciprocal gives an upper bound after the sum is divided by the scale. -/
theorem le_scaledSum (scale : ℕ) (hs : 0 < scale) (k : D → ℕ) (hk : ∀ d, 0 < k d) :
    ∑ d, 1 / (k d : ℚ) ≤ (scaledSum scale k : ℚ) / scale := by
  simpa only [scaledSum, Nat.cast_sum, sum_div] using
    (sum_le_sum (s := univ) fun d _ => le_faceWeight hs (hk d))

omit [Fintype D] in
/-- Around a vertex, an angle receives at most the smaller of the weights of its
two incident darts. Following the cyclic row from `lo` to `hi` shows that one
weight at `lo` may be replaced by the weight at `hi`. Choosing minimum and
maximum lengths gives the second bound in `compute_fractions`. -/
theorem angle_sum_le (r : Perm D) (s : Finset D) (hr : r.IsCycleOn s)
    (w a : D → ℚ) {lo hi : D} (hlo : lo ∈ s) (hhi : hi ∈ s)
    (hleft : ∀ i ∈ s, a i ≤ w i) (hright : ∀ i ∈ s, a i ≤ w (r i)) :
    ∑ i ∈ s, a i ≤ (∑ i ∈ s, w i) - w lo + w hi := by
  classical
  obtain ⟨n, hn, hend⟩ := hr.exists_pow_eq hlo hhi
  let p (i : ℕ) := (r ^ i) lo
  have hstep (i : ℕ) : p (i+1) = r (p i) := by simp [p, pow_succ', Perm.mul_apply]
  have hm (i : ℕ) : p i ∈ s := hr.1.mapsTo.perm_pow i hlo
  have hinj : Set.InjOn p ↑(range n) :=
    fun _ hx _ hy => hr.injOn_pow_apply hlo ((mem_range.mp hx).trans hn)
      ((mem_range.mp hy).trans hn)
  have hsub : (range n).image p ⊆ s := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hm i
  let loss (i : D) := w i - a i
  have h : w lo - w hi ≤ ∑ i ∈ s, loss i := calc
    _ = ∑ i ∈ range n, (w (p i) - w (p (i+1))) := by
      rw [sum_range_sub' (fun i => w (p i))]
      simp [p, hend]
    _ ≤ ∑ i ∈ range n, loss (p i) := by
      refine sum_le_sum fun i _ => ?_
      rw [hstep]
      exact sub_le_sub_left (hright _ (hm i)) _
    _ = ∑ i ∈ (range n).image p, loss i := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => sub_nonneg.mpr (hleft i hi))
  simp only [loss, sum_sub_distrib] at h
  linarith


open Faces

/-- The graph-only transition used by shortest-path BFS on the rows' darts. -/
def rowStep {rows : List (List ℕ)} (h : Valid rows) : Dart rows → Dart rows → Prop :=
  Eligible (fun d => d.val.1) (alpha h)

/-- Every facial step is eligible, because each vertex rotation cycles through its entire row. -/
theorem rowStep_facePerm {rows : List (List ℕ)} (h : Valid rows) (d : Dart rows) :
    rowStep h d (facePerm h d) := by
  let x := alpha h d
  change x.val.1 = x.val.1 ∧ (rho rows x = x ↔ ∀ a : Dart rows,
    a.val.1 = x.val.1 → a = rho rows x)
  refine ⟨rfl, ⟨fun hx a ha => ?_, fun hu => (hu x rfl).symm⟩⟩
  rw [hx]
  exact ((rho_sameCycle_iff h x a).2 ha.symm).eq_of_left hx |>.symm

/-- The dart bound applies directly to the face count returned by the executable traversal. -/
theorem orbitCount_le_shortest {rows : List (List ℕ)} (h : Valid rows) :
    (orbitCount rows : ℚ) ≤ ∑ d, 1 / (shortest (rowStep h) d : ℚ) := by
  rw [orbitCount_eq h]
  exact face_count_le_shortest _ (rowStep_facePerm h)

omit [Fintype D] in
private theorem reverse_circuit {rev : D → D} {step : D → D → Prop}
    (hr : Function.Injective rev) (hs : ∀ {a b}, step a b → step (rev b) (rev a)) {d : D} {n : ℕ}
    (hc : Circuit step d n) : Circuit step (rev d) n := by
  obtain ⟨hn, p, hp, hpend, hinj, hstep⟩ := hc
  let idx (i : ℕ) := if i = 0 then 0 else n-i
  have he (i : ℕ) : p (idx i) = p (n-i) := by
    by_cases hi : i = 0 <;> simp [idx, hi, hp, hpend]
  refine ⟨hn, fun i => rev (p (idx i)), by simp [idx, hp], by simp [idx, hn.ne', hp], ?_, ?_⟩
  · intro i hi j hj hij
    change i < n at hi
    change j < n at hj
    have hi' : idx i < n := by dsimp [idx]; split <;> omega
    have hj' : idx j < n := by dsimp [idx]; split <;> omega
    have eq := hinj hi' hj' (hr hij)
    dsimp [idx] at eq
    split at eq <;> split at eq <;> omega
  · intro i hi
    change step (rev (p (idx i))) (rev (p (idx (i+1))))
    rw [he i, he (i+1)]
    have h := hs (hstep (n-(i+1)) (by omega))
    rwa [show n-(i+1)+1 = n-i by omega] at h


/-- Reversing the entire circuit preserves its minimum length. In particular one BFS may
supply the bound at both orientations of an undirected edge. -/
theorem shortest_alpha {rows : List (List ℕ)} (h : Valid rows) (d : Dart rows) :
    shortest (rowStep h) (alpha h d) = shortest (rowStep h) d := by
  classical
  have turn {a b : Dart rows} (hab : rowStep h a b) : rowStep h (alpha h b) (alpha h a) := by
    obtain ⟨he, hr⟩ := hab
    change (alpha h a).val.1 = b.val.1 ∧
      (alpha h a = b ↔ ∀ c : Dart rows, c.val.1 = (alpha h a).val.1 → c = alpha h a)
    refine ⟨he.symm, ⟨fun eq c hc => ?_, fun unique => (unique b he).symm⟩⟩
    rw [eq]
    exact hr.mp eq.symm c (hc.trans he.symm)
  have le (d : Dart rows) : shortest (rowStep h) (alpha h d) ≤ shortest (rowStep h) d := by
    have ex : ∃ n, Circuit (rowStep h) d n := ⟨_, face_circuit _ (rowStep_facePerm h) d⟩
    have r := reverse_circuit (step := rowStep h) (alpha h).injective (fun h => turn h)
      (Nat.find_spec ex)
    have er : ∃ n, Circuit (rowStep h) (alpha h d) n := ⟨_, r⟩
    simpa [shortest, ex, er] using Nat.find_min' er r
  exact le_antisymm (le d) (le (alpha h d))


/-- Vertex contribution to the angle bound: replace one largest reciprocal weight
by one smallest weight. A vertex with no darts contributes zero. -/
noncomputable def angleBound (s : Finset D) (w : D → ℚ) : ℚ :=
  if h : s.Nonempty then
    (∑ i ∈ s, w i) - (s.image w).max' (h.image w) + (s.image w).min' (h.image w)
  else 0

omit [Fintype D] in
/-- The angle charge inequality for a whole cyclic row, including empty rows. -/
theorem le_angleBound (r : Perm D) (s : Finset D) (hr : r.IsCycleOn s) (w a : D → ℚ)
    (hleft : ∀ i ∈ s, a i ≤ w i) (hright : ∀ i ∈ s, a i ≤ w (r i)) :
    ∑ i ∈ s, a i ≤ angleBound s w := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨lo, hlo, el⟩ := mem_image.mp ((s.image w).max'_mem (hs.image w))
    obtain ⟨hi, hhi, eh⟩ := mem_image.mp ((s.image w).min'_mem (hs.image w))
    simpa only [angleBound, dite_eq_left hs, ← el, ← eh] using
      angle_sum_le r s hr w a hlo hhi hleft hright
  · simp [not_nonempty_iff_eq_empty.mp hs, angleBound]

/-- The second face-count bound, summed over all vertices. Any reversal-invariant
upper estimates of the reciprocal weights may be used, including upward-rounded weights. -/
theorem orbitCount_le_angles {rows : List (List ℕ)} (h : Valid rows) (w : Dart rows → ℚ)
    (hs : ∀ i, w (alpha h i) = w i)
    (hw : ∀ i, 1 / (shortest (rowStep h) i : ℚ) ≤ w i) :
    (orbitCount rows : ℚ) ≤ ∑ v ∈ range rows.length,
      angleBound (univ.filter (fun d : Dart rows => d.val.1 = v)) w := by
  classical
  let f := facePerm h
  let weight (i : Dart rows) : ℚ := 1 / ((face f i).card : ℚ)
  let a (i : Dart rows) := weight (alpha h i)
  have hweight (i : Dart rows) : weight i ≤ w i := by
    obtain ⟨hp, hle⟩ := shortest_le_face f (rowStep_facePerm h) i
    exact (one_div_le_one_div_of_le (by exact_mod_cast hp) (by exact_mod_cast hle)).trans (hw i)
  rw [orbitCount_eq h, face_count_eq_sum]
  change ∑ i, weight i ≤ _
  rw [← Equiv.sum_comp (alpha h) weight]
  change ∑ i, a i ≤ _
  rw [← sum_fiberwise_of_maps_to (t := range rows.length)
    (g := fun d : Dart rows => d.val.1) (fun i _ => mem_range.mpr (mem_darts.mp i.prop).1) a]
  refine sum_le_sum fun v _ => le_angleBound (rho rows) _ ?_ w a ?_ ?_
  · refine ⟨(rho rows).bijOn (fun _ => ?_), fun x hx y hy => ?_⟩
    · simp
    · apply (rho_sameCycle_iff h x y).2
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      exact hx.trans hy.symm
  · intro i _
    simpa only [a, hs] using hweight (alpha h i)
  · intro i _
    have he : f.SameCycle (alpha h i) (f (alpha h i)) := by simp [Perm.SameCycle.rfl]
    change 1 / ((face f (alpha h i)).card : ℚ) ≤ w (rho rows i)
    rw [face_eq he]
    exact hweight (rho rows i)


/-- Integer units for one vertex. Remove one weight at the shortest length and add
one at the longest length, just as in the histogram around a vertex in the C code. -/
def angleUnits (s : Finset D) (scale : ℕ) (k : D → ℕ) : ℕ :=
  if hs : s.Nonempty then
    (∑ d ∈ s, faceWeight scale (k d)) - faceWeight scale ((s.image k).min' (hs.image k)) +
      faceWeight scale ((s.image k).max' (hs.image k))
  else 0

omit [Fintype D] in
private theorem angleBound_le_units (s : Finset D) (scale : ℕ) (k : D → ℕ) :
    angleBound s (fun d => (faceWeight scale (k d) : ℚ) / scale) ≤
      (angleUnits s scale k : ℚ) / scale := by
  classical
  by_cases hs : s.Nonempty
  · let w (i : D) : ℚ := (faceWeight scale (k i) : ℚ) / scale
    obtain ⟨lo, hlo, el⟩ := mem_image.mp ((s.image k).min'_mem (hs.image k))
    obtain ⟨hi, hhi, eh⟩ := mem_image.mp ((s.image k).max'_mem (hs.image k))
    have hl := (s.image w).le_max' _ (mem_image_of_mem w hlo)
    have hh := (s.image w).min'_le _ (mem_image_of_mem w hhi)
    have hsub : faceWeight scale (k lo) ≤ ∑ d ∈ s, faceWeight scale (k d) :=
      single_le_sum (f := fun i => faceWeight scale (k i)) (by intros; omega) hlo
    change angleBound s w ≤ _
    simp only [angleBound, angleUnits, dite_eq_left hs, ← el, ← eh, Nat.cast_add,
      Nat.cast_sub hsub, Nat.cast_sum, add_div, sub_div, sum_div]
    exact add_le_add (sub_le_sub_left hl _) hh
  · simp [angleBound, angleUnits, not_nonempty_iff_eq_empty.mp hs]

/-- The integer face bound produced by the angle histograms. -/
noncomputable def vertexUnits {rows : List (List ℕ)} (h : Valid rows) (scale : ℕ) : ℕ :=
  ∑ v ∈ range rows.length, angleUnits (univ.filter (fun d : Dart rows => d.val.1 = v))
    scale (shortest (rowStep h))

private theorem floor_units {n units scale : ℕ} (hs : 0 < scale)
    (h : (n : ℚ) ≤ (units : ℚ) / scale) : n ≤ units / scale := by
  apply (Nat.le_div_iff_mul_le hs).2
  exact_mod_cast (le_div_iff₀ (by exact_mod_cast hs)).1 h

/-- Flooring the scaled vertex bound gives an integral upper bound for the face count. -/
theorem orbitCount_le_vertexUnits {rows : List (List ℕ)} (h : Valid rows) {scale : ℕ}
    (hs : 0 < scale) : orbitCount rows ≤ vertexUnits h scale / scale := by
  let k := shortest (rowStep h)
  let w (i : Dart rows) : ℚ := (faceWeight scale (k i) : ℚ) / scale
  have hw (i : Dart rows) : 1 / (k i : ℚ) ≤ w i :=
    le_faceWeight hs (shortest_le_face _ (rowStep_facePerm h) i).1
  apply floor_units hs
  refine (orbitCount_le_angles h w (fun i => by simp [w, k, shortest_alpha]) hw).trans ?_
  simp only [vertexUnits, Nat.cast_sum, sum_div]
  exact sum_le_sum fun v _ => angleBound_le_units _ _ _

/-- The first integer bound uses the sorted dart histogram, with the `top.card` largest
entries set to the length at `d`. The code chooses a dart of maximum shortest length. -/
theorem orbitCount_le_topUnits {rows : List (List ℕ)} (h : Valid rows) {scale : ℕ}
    (hs : 0 < scale) (d : Dart rows) (top : Finset (Dart rows))
    (hc : top.card = shortest (rowStep h) d)
    (ho : ∀ i ∈ top, ∀ j ∉ top, shortest (rowStep h) j ≤ shortest (rowStep h) i) :
    orbitCount rows ≤ scaledSum scale
      (fun i => if i ∈ top then shortest (rowStep h) d else shortest (rowStep h) i) / scale := by
  let k := shortest (rowStep h)
  let promoted (i : Dart rows) := if i ∈ top then k d else k i
  have hp (i : Dart rows) := (shortest_le_face _ (rowStep_facePerm h) i).1
  apply floor_units hs
  refine le_trans ?_ (le_scaledSum scale hs promoted (fun i => by
    dsimp [promoted]; split <;> apply hp))
  rw [orbitCount_eq h, ← sum_add_sum_compl top (fun i => 1 / (promoted i : ℚ))]
  have ht := face_count_le_top (facePerm h) k d top hp
    (fun i => (shortest_le_face _ (rowStep_facePerm h) i).2) hc ho
  convert ht using 1
  congr 1
  · exact sum_congr rfl (fun i hi => by simp [promoted, hi])
  · exact sum_congr rfl (fun i hi => by simp [promoted, mem_compl.mp hi])

/-- The nonnegative genus lower bound obtained after flooring the integer face estimate. -/
def lowerGenus (v e faceUpper : ℕ) : ℕ := (3 + e - v - faceUpper) / 2

/-- An integer face upper bound gives a safe starting genus and hence safe target pruning. -/
theorem lowerGenus_le {v e f genus upper : ℕ} (euler : 2 * genus + v + f = 2 + e)
    (bound : f ≤ upper) : lowerGenus v e upper ≤ genus := by
  unfold lowerGenus
  omega


/-- A positive eligible return, as recognized by breadth-first search on directed darts. -/
def ReturnWalk (step : D → D → Prop) (d : D) (n : ℕ) : Prop :=
  0 < n ∧ ∃ p : ℕ → D, p 0 = d ∧ p n = d ∧ ∀ i < n, step (p i) (p (i + 1))

omit [Fintype D] in
/-- A shortest positive return has distinct darts before closure. Deleting the segment
between equal darts would otherwise give a strictly shorter positive return. -/
theorem circuit_of_min_return (step : D → D → Prop) (d : D) (n : ℕ)
    (walk : ReturnWalk step d n) (least : ∀ m, ReturnWalk step d m → n ≤ m) :
    Circuit step d n := by
  obtain ⟨hn, p, hp, hend, hnext⟩ := walk
  have distinct {i j : ℕ} (hij : i < j) (hj : j < n) (eq : p i = p j) : False := by
    let gap := j - i
    let q (a : ℕ) := if a < i then p a else p (a + gap)
    have hgap : i + gap = j := by dsimp [gap]; omega
    have end' : n-gap + gap = n := by dsimp [gap]; omega
    have start' : q 0 = d := by
      by_cases hi : i = 0
      · subst i; simpa [q, gap] using eq.symm.trans hp
      · simp [q, Nat.pos_of_ne_zero hi, hp]
    have last' : q (n-gap) = d := by
      have h : ¬ n-gap < i := by dsimp [gap]; omega
      simp [q, h, end', hend]
    have nxt (a : ℕ) (ha : a < n-gap) : step (q a) (q (a+1)) := by
      by_cases h : a+1 < i
      · simpa [q, h, show a < i by omega] using hnext a (by omega)
      · by_cases e : a+1 = i
        · have qi : q i = p i := by simp [q, hgap, ← eq]
          rw [e, qi]
          simpa [q, show a < i by omega, ← e] using hnext a (by omega)
        · have hi : ¬ a < i := by omega
          simpa [q, hi, h, Nat.add_right_comm] using hnext (a+gap) (by omega)
    have bad := least (n-gap) ⟨by dsimp [gap]; omega, q, start', last', nxt⟩
    dsimp [gap] at bad
    omega
  refine ⟨hn, p, hp, hend, fun {i} hi {j} hj eq => ?_, hnext⟩
  rcases lt_trichotomy i j with h | h | h
  · exact (distinct h hj eq).elim
  · exact h
  · exact (distinct h hi eq.symm).elim

omit [Fintype D] in
/-- The least length recognized by positive-return search equals the facial-like walk minimum. -/
theorem shortest_eq_of_min_return (step : D → D → Prop) (d : D) (n : ℕ)
    (walk : ReturnWalk step d n) (least : ∀ m, ReturnWalk step d m → n ≤ m) :
    shortest step d = n := by
  classical
  have c := circuit_of_min_return step d n walk least
  have ex : ∃ m, Circuit step d m := ⟨_, c⟩
  have hw : ∀ m, Circuit step d m → ReturnWalk step d m := by
    rintro m ⟨hm, q, hq, he, _, hs⟩
    exact ⟨hm, q, hq, he, hs⟩
  simpa [shortest, ex] using le_antisymm (Nat.find_min' ex c) (least _ (hw _ (Nat.find_spec ex)))


/-- A circuit's distinct directed edges bound its length by the number of darts. -/
theorem Circuit.le_card {step : D → D → Prop} {d : D} {n : ℕ} (h : Circuit step d n) :
    n ≤ Fintype.card D := by
  obtain ⟨_, p, _, _, hi, _⟩ := h
  simpa using Fintype.card_le_of_injective (fun i : Fin n => p i)
    (fun i j e => Fin.ext (hi i.isLt j.isLt e))

end MultiGenus.Bounds
