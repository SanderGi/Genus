/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.Certificate
public import MultiGenus.Search
public import MultiGenus.Bounds

/-! # Length bounds for the face candidates of a simple graph -/

@[expose] public section

namespace Page.FaceBounds

open MultiGenus MultiGenus.Rotations MultiGenus.Faces Page.Certificate

/-- A complete cover uses exactly two dart positions per edge. -/
theorem total_length_eq {n edges fs} (hc : check n edges fs = true) :
    (fs.map List.length).sum = 2 * edges.length := by
  have eq := (check_flatten_perm hc).length_eq
  simpa [Certificate.universe, two_mul] using eq

/-- A single face can use at most the entire dart budget. -/
theorem length_le_twice_edges {n edges fs f} (hc : check n edges fs = true) (hf : f ∈ fs) :
    f.length ≤ 2 * edges.length := by
  rw [← total_length_eq hc]
  exact List.le_sum_of_mem (List.mem_map_of_mem hf)

private theorem edge_of_dart {n edges fs f d} (hc : check n edges fs = true)
    (hf : f ∈ fs) (hd : d ∈ f) : d.2 ∈ neighbors edges d.1 :=
  mem_neighbors.mpr (mem_universe.mp
    ((check_flatten_perm hc).mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, hd⟩)))

private theorem endpoints_ne {n edges} (G : SimpleInput n edges) {u v}
    (adj : v ∈ neighbors edges u) : u ≠ v :=
  (mem_neighbors.mp adj).elim (fun h => (G.ordered _ h).ne) (fun h => (G.ordered _ h).ne.symm)

/-- A monogon would traverse a loop. -/
theorem length_ne_one {n edges fs f} (G : SimpleInput n edges) (hc : check n edges fs = true)
    (hf : f ∈ fs) : f.length ≠ 1 := by
  intro one
  obtain ⟨⟨u, v⟩, rfl⟩ := List.length_eq_one_iff.mp one
  have turn := matches_readRows hc _ hf (u, v) (.head _)
  have eq : u = v := congrArg Prod.fst turn
  exact endpoints_ne G (edge_of_dart hc hf (.head _)) eq

/-- An immediate reversal in a certified walk occurs exactly at a degree-one vertex. -/
theorem reverses_iff_leaf {n edges fs f u v} (G : SimpleInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (hd : (u, v) ∈ f) :
    f.formPerm (u, v) = (v, u) ↔ (neighbors edges v).length = 1 := by
  let r := readRows n edges fs
  have legal : Legal n edges r := (readRows_of_check G hc).1
  have adj := edge_of_dart hc hf hd
  have hv : v < n := G.neighbor_lt adj
  have perm : (row r v).Perm (neighbors edges v) := legal.2 v hv
  have mem : u ∈ row r v := perm.mem_iff.mpr (mem_neighbors.mpr (mem_neighbors.mp adj).symm)
  rw [matches_readRows hc f hf _ hd]
  change (v, (row r v).formPerm u) = (v, u) ↔ _
  simp only [Prod.mk.injEq, true_and]
  rw [List.formPerm_apply_mem_eq_self_iff _ ((valid_of_legal G legal).nodup v) u mem,
    perm.length_eq]
  have := List.length_pos_of_mem (perm.mem_iff.mp mem)
  omega

private theorem unique_neighbor {edges : List Edge} {u v : Nat} (adj : v ∈ neighbors edges u)
    (one : (neighbors edges u).length = 1) : neighbors edges u = [v] := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp one
  rw [hx, List.mem_singleton] at adj
  rwa [adj]

/-- A cellular digon in a connected simple graph forces the entire input to be K2. -/
theorem digon_forces_K2 {n edges fs f} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (two : f.length = 2) :
    n = 2 ∧ edges = [(0, 1)] := by
  obtain ⟨⟨u, v⟩, ⟨w, z⟩, rfl⟩ := List.length_eq_two.mp two
  let d := (u, v)
  let e := (w, z)
  have step₁ := matches_readRows hc _ hf d (.head _)
  have step₂ := matches_readRows hc _ hf e (by simp [e])
  have eq₁ : w = v := by simpa [d, List.formPerm_pair, faceStep] using congrArg Prod.fst step₁
  have eq₂ : u = z := by simpa [e, List.formPerm_pair, faceStep] using congrArg Prod.fst step₂
  subst w z
  have hv := (reverses_iff_leaf G hc hf (List.mem_cons_self (a := (u, v)))).mp
    (by simp)
  have hu := (reverses_iff_leaf G hc hf (by simp : (v, u) ∈ [(u, v), (v, u)])).mp
    (by simp)
  have adj : v ∈ neighbors edges u := edge_of_dart hc hf (.head _)
  have rev : u ∈ neighbors edges v := mem_neighbors.mpr (mem_neighbors.mp adj).symm
  have atU := unique_neighbor adj hu
  have atV := unique_neighbor rev hv
  have un := G.neighbor_lt rev
  have vn := G.neighbor_lt adj
  have reach (x : Nat) (hx : x < n) : x = u ∨ x = v := by
    have path := con.2 u un x hx
    clear hx
    induction path with
    | refl => exact Or.inl rfl
    | tail _ hy ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (by simpa only [atU, List.mem_singleton] using hy)
      · exact Or.inl (by simpa only [atV, List.mem_singleton] using hy)
  have hn : n = 2 := by
    have distinct := endpoints_ne G adj
    by_contra ne
    have h : 2 < n := by omega
    have := reach 0 (by omega)
    have := reach 1 (by omega)
    have := reach 2 h
    omega
  refine ⟨hn, ?_⟩
  have only (a : Edge) (ha : a ∈ edges) : a = (0, 1) := by
    have := G.ordered a ha
    have := G.bounded a ha
    exact Prod.ext (by omega) (by omega)
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil (l := edges) (by
    rintro rfl
    simp [neighbors] at adj)
  have ha := only a (.head _)
  have nil : as = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx =>
    (List.nodup_cons.mp G.nodup).1 ((ha.trans (only x (.tail _ hx)).symm) ▸ hx)
  rw [ha, nil]

private theorem edges_ne_nil {n edges} (con : ConnectedInput n edges) (hn : 3 ≤ n) :
    edges ≠ [] := by
  rintro rfl
  obtain ⟨v, hv⟩ := SimpleInput.exists_neighbor con (by omega) 0 (by omega)
  simp [neighbors] at hv

/-- A connected simple graph on at least three vertices has facial length at least three. -/
theorem three_le_length {n edges fs f} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hn : 3 ≤ n) (hc : check n edges fs = true) (hf : f ∈ fs) : 3 ≤ f.length := by
  have pos := List.length_pos_iff.mpr (check_face (edges_ne_nil con hn) hc hf).1
  have one := length_ne_one G hc hf
  have two : f.length ≠ 2 := fun h => (by have := (digon_forces_K2 G con hc hf h).1; omega)
  omega

/-- No three successive edges of the input return to their starting vertex. -/
def TriangleFree (edges : List Edge) : Prop :=
  ∀ a b c, b ∈ neighbors edges a → c ∈ neighbors edges b → a ∉ neighbors edges c

/-- Excluding triangles raises the minimum facial length from three to four. -/
theorem four_le_length {n edges fs f} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hn : 3 ≤ n) (ht : TriangleFree edges) (hc : check n edges fs = true) (hf : f ∈ fs) :
    4 ≤ f.length := by
  have lower := three_le_length G con hn hc hf
  by_contra! small
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp (show f.length = 3 by omega)
  have ⟨_, _, _, chain⟩ := admissible_of_check (edges_ne_nil con hn) hc hf
  change List.IsChain Walks.Fits [a, b, c, a] at chain
  have ab := chain.rel
  have bc := chain.tail.rel
  have ca := chain.tail.tail.rel
  change a.2 = b.1 at ab
  change b.2 = c.1 at bc
  change c.2 = a.1 at ca
  have ha := edge_of_dart hc hf (List.mem_cons_self (a := a))
  have hb := edge_of_dart hc hf (by simp : b ∈ [a, b, c])
  have hc' := edge_of_dart hc hf (by simp : c ∈ [a, b, c])
  exact ht a.1 b.1 c.1 (ab ▸ ha) (bc ▸ hb) (ca ▸ hc')

/-- Test whether some directed edge extends by one neighbor to a triangle. -/
def hasTriangle (edges : List Edge) : Bool :=
  (Certificate.universe edges).any fun d =>
    (neighbors edges d.2).any fun c => d.1 ∈ neighbors edges c

theorem hasTriangle_eq_false {edges} : hasTriangle edges = false ↔ TriangleFree edges := by
  simp only [hasTriangle, List.any_eq_false, List.any_eq_true, decide_eq_true_eq, not_exists,
    not_and]
  constructor
  · intro test a b c ab
    exact test (a, b) (mem_universe.mpr (mem_neighbors.mp ab)) c
  · rintro free ⟨a, b⟩ ab c bc
    exact free a b c (mem_neighbors.mpr (mem_universe.mp ab)) bc

/-- The initial face-length layer, allowing small inputs to use the full range. -/
def minLength (n : Nat) (edges : List Edge) : Nat :=
  if n < 3 then 0 else if hasTriangle edges then 3 else 4

theorem minLength_le {n edges fs f} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) : minLength n edges ≤ f.length := by
  unfold minLength
  split
  · exact Nat.zero_le _
  · split
    · exact three_le_length G con (by omega) hc hf
    · exact four_le_length G con (by omega) (hasTriangle_eq_false.mp (by simp_all)) hc hf

private theorem min_mul_length {fs : List Face} {k : Nat} (h : ∀ f ∈ fs, k ≤ f.length) :
    fs.length * k ≤ (fs.map List.length).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have head := h f (.head _)
    have tail := ih (fun w hw => h w (.tail _ hw))
    simpa only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons, Nat.add_comm]
      using Nat.add_le_add tail head

/-- Reserve the minimum number of darts for every other face in a target cover. -/
def faceCap (n : Nat) (edges : List Edge) (k : Nat) : Nat :=
  2 * edges.length - (k - 1) * minLength n edges

theorem length_le_cap {n edges fs f} (G : SimpleInput n edges) (con : ConnectedInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) : f.length ≤ faceCap n edges fs.length := by
  have perm := List.perm_cons_erase hf
  have bound := min_mul_length (fs := fs.erase f)
    (fun w hw => minLength_le G con hc (List.mem_of_mem_erase hw))
  have total := (perm.map List.length).sum_eq
  rw [total_length_eq hc] at total
  simp only [List.map_cons, List.sum_cons] at total
  have len := perm.length_eq
  simp only [List.length_cons] at len
  rw [faceCap, len, Nat.add_sub_cancel]
  omega

/-- Floor the dart-budget bound on faces, then round Euler's genus lower bound upwards. -/
def lowerGenus (n : Nat) (edges : List Edge) : Nat :=
  if n < 3 then 0 else Bounds.lowerGenus n edges.length (2 * edges.length / minLength n edges)

theorem lowerGenus_le_minimum {n edges} (G : SimpleInput n edges) (con : ConnectedInput n edges) :
    lowerGenus n edges ≤ minimumGenus n edges := by
  unfold lowerGenus
  split
  · exact Nat.zero_le _
  · rename_i hn
    obtain ⟨fs, hc, euler⟩ := (realizes_iff_check G).mp (minimumGenus_isLeast G con).1
    have all := min_mul_length (fun f hf => minLength_le G con hc hf)
    rw [total_length_eq hc] at all
    have pos : 0 < minLength n edges := by
      simp only [minLength, hn, ↓reduceIte]
      split <;> decide
    exact Bounds.lowerGenus_le (by omega : 2 * minimumGenus n edges + n + fs.length =
      2 + edges.length) ((Nat.le_div_iff_mul_le pos).mpr all)

end Page.FaceBounds
