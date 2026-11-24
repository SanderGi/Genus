/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.WalkSearch
public import MultiGenus.Genus
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Pairing

/-! # Executable initial genus bound from the input graph

The canonical dart set contains both orientations of every input edge. Shortest positive
returns use its graph of eligible turns. The sorted list and vertex histograms reuse the
same table of BFS lengths. The soundness proof identifies the canonical dart set with the
darts of an arbitrary legal rotation, without consulting that rotation during computation.
-/

@[expose] public section

namespace MultiGenus.LowerBound

open Finset Rotations Faces Bounds

/-- Precision used by both C implementations. Each dart weight is rounded upwards. -/
def scale : ℕ := 3603600000000

/-- Both orientations of the undirected input edges. -/
def inputDarts (edges : List Edge) : Finset Edge :=
  edges.toFinset ∪ edges.toFinset.image Prod.swap

private theorem mem_inputDarts (edges : List Edge) (d : Edge) :
    d ∈ inputDarts edges ↔ d ∈ edges ∨ d.swap ∈ edges := by
  simp [inputDarts, Prod.swap_eq_iff_eq_swap]

private theorem inputDarts_eq {n : ℕ} {edges : List Edge} {rows : Rows}
    (G : SimpleInput n edges) (hr : Legal n edges rows) : inputDarts edges = darts rows := by
  ext ⟨u,v⟩
  rw [mem_inputDarts, mem_darts]
  change ((u,v) ∈ edges ∨ (v,u) ∈ edges) ↔ _
  rw [← mem_neighbors]
  constructor
  · intro h
    have hu := G.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp h).symm)
    exact ⟨hr.1 ▸ hu, (hr.2 u hu).mem_iff.mpr h⟩
  · rintro ⟨hu, hv⟩
    exact (hr.2 u (hr.1 ▸ hu)).mem_iff.mp hv

/-- Eligible adjacency uses only the directed incidence set. -/
def turn {ds : Finset Edge} (a b : ↥ds) : Prop :=
  b.val.1 = a.val.2 ∧ (b.val.2 = a.val.1 ↔ ∀ c : ↥ds, c.val.1 = b.val.1 → c = b)

instance {ds : Finset Edge} : DecidableRel (@turn ds) :=
  fun _ _ => by unfold turn; infer_instance

private theorem turn_eq {rows : Rows} (h : Valid rows) : @turn (darts rows) = rowStep h := by
  funext a b
  apply propext
  change (_ ∧ (_ ↔ _)) ↔ b.val.1 = a.val.2 ∧ (b = alpha h a ↔ _)
  apply and_congr_right
  intro he
  have e : b.val.2 = a.val.1 ↔ b = alpha h a :=
    ⟨fun e => Subtype.ext (Prod.ext he e), fun eq => congrArg (fun d : Dart rows => d.val.2) eq⟩
  rw [e]

/-- A deterministic enumeration of the directed incidence set. Pairing the two endpoint
numbers provides a linear ordering independent of the input rotation. -/
def dartList (ds : Finset Edge) : List ↥ds :=
  let key (d : ↥ds) := Nat.pairEquiv d.val
  let rel (a b : ↥ds) := key a ≤ key b
  let _ : IsTrans _ rel := ⟨fun _ _ _ h h' => le_trans h h'⟩
  let _ : Std.Antisymm rel := ⟨fun _ _ h h' =>
    Subtype.ext (Nat.pairEquiv.injective (le_antisymm h h'))⟩
  let _ : Std.Total rel := ⟨fun a b => Nat.le_total (key a) (key b)⟩
  univ.sort rel

private theorem dartList_spec (ds : Finset Edge) :
    (dartList ds).Nodup ∧ ∀ i, i ∈ dartList ds := by simp [dartList]

/-- Choose the darts with the largest local lengths, truncating at the end of the list. -/
def largest {D : Type*} [DecidableEq D] (xs : List D) (k : D → ℕ) (m : ℕ) : Finset D :=
  ((xs.mergeSort fun a b => decide (k b ≤ k a)).take m).toFinset

private theorem largest_spec {D : Type*} [DecidableEq D] (xs : List D) (k : D → ℕ)
    (m : ℕ) (hd : xs.Nodup) (all : ∀ d, d ∈ xs) (hm : m ≤ xs.length) :
    (largest xs k m).card = m ∧ ∀ i ∈ largest xs k m, ∀ j ∉ largest xs k m, k j ≤ k i := by
  let cmp (a b : D) := decide (k b ≤ k a)
  let ys := xs.mergeSort cmp
  have perm : ys.Perm xs := List.mergeSort_perm ..
  have ordered : ys.Pairwise (fun a b => k b ≤ k a) := by
    simpa only [cmp, decide_eq_true_eq] using List.pairwise_mergeSort (le := cmp)
      (by simpa [cmp] using (fun a b c (hab : k b ≤ k a) (hbc : k c ≤ k b) =>
        hbc.trans hab)) (by simpa [cmp] using (fun a b => le_total (k b) (k a))) xs
  change (ys.take m).toFinset.card = m ∧ _
  refine ⟨by rw [List.toFinset_card_of_nodup (perm.nodup_iff.mpr hd |>.take),
    List.length_take, perm.length_eq, Nat.min_eq_left hm], ?_⟩
  intro i hi j hj
  change i ∈ (ys.take m).toFinset at hi
  change j ∉ (ys.take m).toFinset at hj
  have hj' : j ∈ ys.take m ++ ys.drop m := by
    rw [List.take_append_drop]; exact perm.mem_iff.mpr (all j)
  exact ordered.rel_of_mem_take_of_mem_drop (List.mem_toFinset.mp hi)
    ((List.mem_append.mp hj').resolve_left (fun h => hj (List.mem_toFinset.mpr h)))

/-- Floor the smaller of the global and vertex histograms. The triangular-face estimate
also applies whenever all shortest lengths are at least three. -/
def histogramBound (n : ℕ) (ds : Finset Edge) (k : ↥ds → ℕ) : ℕ :=
  let m := univ.sup k
  let top := largest (dartList ds) k m
  let global := scaledSum scale (fun i => if i ∈ top then m else k i)
  let localUnits := ∑ v ∈ range n, angleUnits (univ.filter (fun d : ↥ds => d.val.1 = v)) scale k
  let fractions := min global localUnits / scale
  if ∀ d, 3 ≤ k d then min fractions (ds.card / 3) else fractions

/-- Integer upper bound on the number of faces. Both histograms reuse the BFS length table. -/
def faceUpper (n : ℕ) (ds : Finset Edge) : ℕ :=
  let table := (dartList ds).map (fun d => (d, WalkSearch.shortestReturn turn d))
  histogramBound n ds (fun d => (table.lookup d).getD 0)

/-- Initial lower genus for iterative deepening. Graphs of order at most two have bound zero. -/
def initial (n : ℕ) (edges : List Edge) : ℕ :=
  if n ≤ 2 then 0 else lowerGenus n edges.length (faceUpper n (inputDarts edges))


private theorem density {rows : Rows} (h : Valid rows) (hk : ∀ i, 3 ≤ shortest (rowStep h) i) :
    orbitCount rows ≤ (darts rows).card / 3 := by
  have hq : (orbitCount rows : ℚ) ≤ ∑ _ : Dart rows, 1 / (3 : ℚ) := by
    refine (orbitCount_le_shortest h).trans (sum_le_sum fun i _ => ?_)
    exact one_div_le_one_div_of_le (by decide) (by exact_mod_cast hk i)
  simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] at hq
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  exact_mod_cast (show (orbitCount rows : ℚ) * 3 ≤ (darts rows).card by linarith)

private theorem orbitCount_le_faceUpper {rows : Rows} (h : Valid rows) (x : Dart rows) :
    orbitCount rows ≤ faceUpper rows.length (darts rows) := by
  let ds := darts rows
  let xs := dartList ds
  let k := shortest (rowStep h)
  let m := univ.sup k
  let top := largest xs k m
  obtain ⟨hnodup, hall⟩ := dartList_spec ds
  have table (i : Dart rows) :
      ((xs.map fun d => (d, WalkSearch.shortestReturn turn d)).lookup i).getD 0 = k i := by
    rw [List.lookup_graph _ (hall i), Option.getD_some, WalkSearch.shortestReturn_eq_shortest,
      turn_eq h]
  have allcard : xs.length = Fintype.card (Dart rows) := by
    have heu : xs.toFinset = univ := eq_univ_of_forall fun i => List.mem_toFinset.mpr (hall i)
    rw [← List.toFinset_card_of_nodup hnodup, heu, card_univ]
  obtain ⟨d, _, he⟩ := exists_mem_eq_sup univ ⟨x, mem_univ _⟩ k
  have hm : m ≤ xs.length := by
    change univ.sup k ≤ xs.length
    rw [he, allcard]
    exact (shortest_le_face _ (rowStep_facePerm h) d).2.trans (card_le_univ _)
  obtain ⟨hc, ho⟩ := largest_spec xs k m hnodup hall hm
  let global := scaledSum scale (fun i => if i ∈ top then m else k i)
  have hg : orbitCount rows ≤ global / scale := by
    change orbitCount rows ≤ scaledSum scale (fun i => if i ∈ top then m else k i) / scale
    have em : m = k d := he
    rw [em]
    exact orbitCount_le_topUnits h (by decide : 0 < scale) d top (hc.trans em) ho
  have hv := orbitCount_le_vertexUnits h (by decide : 0 < scale)
  have both : orbitCount rows ≤ min global (vertexUnits h scale) / scale := by
    rcases le_total global (vertexUnits h scale) with h | h
    · simpa [min_eq_left h] using hg
    · simpa [min_eq_right h] using hv
  change orbitCount rows ≤ histogramBound rows.length ds _
  rw [funext table]
  change orbitCount rows ≤ if ∀ i, 3 ≤ k i then
    min (min global (vertexUnits h scale) / scale) (ds.card / 3)
    else min global (vertexUnits h scale) / scale
  split
  · exact le_min both (density h ‹_›)
  · exact both

/-- Iterative deepening may start at `initial` for every legal rotation of a connected
simple input. The order-one and order-two cases are included. -/
theorem initial_le {n : ℕ} {edges : List Edge} {rows : Rows} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (hr : Legal n edges rows) :
    initial n edges ≤ genusOf n edges.length rows := by
  unfold initial
  split
  · exact Nat.zero_le _
  · rename_i hn
    have nontriv : 1 < n := by omega
    obtain ⟨x, _⟩ := Map.origin_surjective hr con nontriv (⟨0, con.1⟩ : Fin n)
    have many : rows ≠ [[]] := by
      intro eq
      have len := hr.1
      rw [eq] at len
      change 1 = n at len
      omega
    have counts := orbitCount_le_faceUpper (valid_of_legal G hr) x
    rw [hr.1, ← inputDarts_eq G hr] at counts
    apply lowerGenus_le (f := faceCount rows)
    · have eu := euler_genus G con hr
      omega
    · simpa only [faceCount, ite_eq_right many] using counts

end MultiGenus.LowerBound
