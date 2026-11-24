/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.FaceBounds
public import Page.Layers
public import Page.Optimize
import Mathlib.Data.List.Flatten

/-! # Pivot, packing, and symmetry bounds for materialized face search -/

@[expose] public section

namespace Page.Pruning

open MultiGenus MultiGenus.Rotations MultiGenus.Faces Page.Certificate

/-- Any uncovered dart can be used as a pivot: put it at the front of the multiset of
remaining darts and invoke the ordinary exact-cover search. -/
theorem dfs_at_pivot {pool check k remaining chosen pending}
    (stable : ExactCover.Invariant check) (len : pending.length = k)
    (cov : pending.flatten.Perm remaining) (ok : check (pending ++ chosen) = true)
    (nonempty : ∀ f ∈ pending, f ≠ []) (rooted : ∀ f ∈ pending, ∀ d ∈ f,
      ∃ g ∈ pool d, f.IsRotated g) {d : Walks.Dart} (hd : d ∈ remaining) :
    (ExactCover.dfs (ExactCover.fromLists pool) check k (d :: remaining.erase d) chosen).isSome :=
  ExactCover.dfs_complete _ _ stable _ _ _ _ len (cov.trans (List.perm_cons_erase hd))
    ok nonempty rooted

/-- Lower bound on the dart sum when the shortest length is `s` and all other faces
have length at least `t`. -/
theorem packing_cost (ls : List Nat) (s t : Nat) (gap : ∀ x ∈ ls, x = s ∨ t ≤ x) :
    ls.count s * s + (ls.length - ls.count s) * t ≤ ls.sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have bound := ih (fun y hy => gap y (.tail _ hy))
    have le := List.count_le_length (a := s) (l := xs)
    rcases gap x (.head _) with rfl | hx
    · simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left bound x
    · by_cases eq : x = s
      · subst x
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left bound s
      · have sub : xs.length + 1 - xs.count s = xs.length - xs.count s + 1 := by omega
        simpa [List.count_cons, eq, sub, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using Nat.add_le_add bound hx

/-- Rounding up the dart deficit gives the minimum number of shortest faces needed
by a length composition with a strictly larger second length. -/
theorem minimum_shortest (ls : List Nat) {s t : Nat} (st : s < t)
    (gap : ∀ x ∈ ls, x = s ∨ t ≤ x) :
    ((ls.length * t - ls.sum) + (t - s) - 1) / (t - s) ≤ ls.count s := by
  apply (Nat.div_le_iff_le_mul_add_pred (Nat.sub_pos_of_lt st)).mpr
  have cost := packing_cost ls s t gap
  have le := List.count_le_length (a := s) (l := ls)
  have total : ls.length * t = (ls.length - ls.count s) * t + ls.count s * t := by
    rw [← Nat.add_mul, Nat.sub_add_cancel le]
  have save : (t - s) * ls.count s + ls.count s * s = ls.count s * t := by
    rw [Nat.mul_comm (ls.count s) s, ← Nat.add_mul, Nat.sub_add_cancel st.le, Nat.mul_comm]
  omega

/-- Equal-length admissible walks that use pairwise disjoint directed darts. -/
def Packing (edges : List Edge) (s : Nat) (ps : List Face) : Prop :=
  ps.flatten.Nodup ∧ ∀ f ∈ ps, f.length = s ∧ Walks.Admissible (Certificate.universe edges) f

/-- A dart-disjoint packing uses each vertex as a dart origin at most its degree times. -/
theorem Packing.vertex_capacity {edges s ps} (hp : Packing edges s ps) (v : Nat) :
    (ps.flatten.filter (fun d => d.1 == v)).length ≤ (neighbors edges v).length := by
  have sub : ps.flatten.filter (fun d => d.1 == v) ⊆ (neighbors edges v).map (v, ·) := by
    rintro ⟨a,b⟩ h
    obtain ⟨flat, atV⟩ := List.mem_filter.mp h
    obtain ⟨f, hf, hd⟩ := List.mem_flatten.mp flat
    have adj := mem_neighbors.mpr (mem_universe.mp ((hp.2 f hf).2.2.2.1 hd))
    obtain rfl : a = v := beq_iff_eq.mp atV
    exact List.mem_map_of_mem (f := (a, ·)) adj
  simpa using (hp.1.filter _).length_le_of_subset sub

/-- Proving a packing of size `cap+1` impossible caps the count in every complete
certificate. Taking that many shortest faces of a certificate would exhibit a packing. -/
theorem cap_of_no_packing {n edges fs s cap} (G : SimpleInput n edges) (he : edges ≠ [])
    (hc : check n edges fs = true)
    (impossible : ¬ ∃ ps, Packing edges s ps ∧ ps.length = cap + 1) :
    (fs.map List.length).count s ≤ cap := by
  let short := fs.filter fun f => f.length == s
  have len : (fs.map List.length).count s = short.length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    rfl
  by_contra! large
  let ps := short.take (cap + 1)
  have sub : ps.Sublist fs := (List.take_sublist ..).trans List.filter_sublist
  apply impossible
  refine ⟨ps, ⟨List.Nodup.sublist sub.flatten
    ((check_flatten_perm hc).nodup_iff.mpr (universe_nodup G)), ?_⟩, ?_⟩
  · intro f hf
    have inside : f ∈ short := List.mem_of_mem_take hf
    exact ⟨beq_iff_eq.mp (List.mem_filter.mp inside).2, admissible_of_check he hc (sub.subset hf)⟩
  · simp [ps, List.length_take, Nat.min_eq_left (show cap + 1 ≤ short.length by omega)]

/-- The native greedy upper bound after reserving a future face. If the second shortest
length is unknown (zero), the next unseen length is the lower bound on nonshort faces. -/
def futureFit (total shortest second cap next : Nat) : Nat :=
  if shortest = 0 ∨ total < next then 0 else
    let t := if second = 0 then next else min second next
    let room := total - next
    let m := min (room / shortest) cap
    1 + m + (room - m * shortest) / t

private theorem fit_arith {s t c k room cap : Nat}
    (hs : 0 < s) (st : s ≤ t) (le : c ≤ k) (pack : c ≤ cap)
    (cost : c * s + (k - c) * t ≤ room) :
    k ≤ min (room / s) cap + (room - min (room / s) cap * s) / t := by
  let m := min (room / s) cap
  have cm : c ≤ m := le_min ((Nat.le_div_iff_mul_le hs).mpr (by omega)) pack
  have ms : m * s ≤ room := (Nat.le_div_iff_mul_le hs).mp (min_le_left ..)
  by_cases km : k ≤ m
  · exact le_trans km (Nat.le_add_right ..)
  change k ≤ m + (room - m * s) / t
  suffices div : k - m ≤ (room - m * s) / t by omega
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  have h₁ := Nat.sub_add_cancel cm
  have h₂ := Nat.sub_add_cancel (show m ≤ k by omega)
  have h₃ := Nat.sub_add_cancel le
  have cheaper := Nat.mul_le_mul_left (m - c) st
  have balance : (k - c) * t = (k - m) * t + (m - c) * t := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have paid : m * s = (m - c) * s + c * s := by rw [← Nat.add_mul, h₁]
  omega

/-- If a checked cover contains a face of length at least `next`, reserve that face,
then spend the remaining dart budget on at most `cap` shortest faces. -/
theorem length_le_futureFit {n edges fs s second cap next} (hc : check n edges fs = true)
    (hs : 0 < s) (st : s ≤ if second = 0 then next else min second next)
    (gap : ∀ f ∈ fs, f.length = s ∨ (if second = 0 then next else min second next) ≤ f.length)
    (pack : (fs.map List.length).count s ≤ cap) (future : ∃ f ∈ fs, next ≤ f.length) :
    fs.length ≤ futureFit (2 * edges.length) s second cap next := by
  obtain ⟨f, hf, long⟩ := future
  let rest := fs.erase f
  let ls := rest.map List.length
  have p : fs.Perm (f :: rest) := List.perm_cons_erase hf
  have sum := (p.map List.length).sum_eq
  rw [FaceBounds.total_length_eq hc] at sum
  change 2 * edges.length = f.length + ls.sum at sum
  have count := (p.map List.length).count_eq (a := s)
  change (fs.map List.length).count s = (f.length :: ls).count s at count
  have c : ls.count s ≤ cap := by rw [count, List.count_cons] at pack; split at pack <;> omega
  have bound := packing_cost ls s _ (by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact gap g (List.mem_of_mem_erase hg))
  have cost := fit_arith hs st (List.count_le_length (a := s) (l := ls)) c
    (room := 2 * edges.length - next) (by omega)
  have len : fs.length = ls.length + 1 := by simpa [ls] using p.length_eq
  simp only [futureFit, Nat.ne_of_gt hs, show ¬2 * edges.length < next by omega,
    or_self, ↓reduceIte]
  omega

/-- Exhausting a length layer at a given target forces a longer face at that same target. -/
theorem longer_of_exhausted {stream n edges limit k fs} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (exhausted : Layers.search stream n edges limit k = none)
    (hc : check n edges fs = true) (size : fs.length = k) :
    ∃ f ∈ fs, limit + 1 ≤ f.length := by
  by_contra! all
  have found := Layers.search_complete (stream := stream) (limit := limit) G con hc size
    (fun f hf => by have := all f hf; omega)
  simp [exhausted] at found

/-- The failed target and the future-face bound together permit one genus increment.
The layer exhaustion hypothesis concerns exactly the face count of the current genus. -/
theorem advance_one_genus {stream n edges limit g s second cap} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (lower : g ≤ minimumGenus n edges)
    (exhausted : Layers.search stream n edges limit (faceTarget n edges.length g) = none)
    (hs : 0 < s) (st : s ≤ if second = 0 then limit + 1 else min second (limit + 1))
    (gap : ∀ fs, check n edges fs = true → ∀ f ∈ fs, f.length = s ∨
      (if second = 0 then limit + 1 else min second (limit + 1)) ≤ f.length)
    (pack : ∀ fs, check n edges fs = true → (fs.map List.length).count s ≤ cap)
    (bound : futureFit (2 * edges.length) s second cap (limit + 1) < faceTarget n edges.length g) :
    g + 1 ≤ minimumGenus n edges := by
  by_contra! h
  have eq : minimumGenus n edges = g := by omega
  obtain ⟨fs, hc, euler⟩ := (realizes_iff_check G).mp (eq ▸ (minimumGenus_isLeast G con).1)
  have size : fs.length = faceTarget n edges.length g := by unfold faceTarget; omega
  have future := longer_of_exhausted G con exhausted hc size
  have fit := length_le_futureFit hc hs st (gap _ hc) (pack _ hc) future
  omega

/-- A permutation of natural vertex labels preserving the input vertex set and adjacency. -/
structure Automorphism (n : Nat) (edges : List Edge) where
  /-- Relabel vertices, with an inverse defined on all labels. -/
  label : Equiv.Perm Nat
  /-- Restricting to the first `n` labels gives a permutation of the vertices. -/
  bounded : ∀ v, label v < n ↔ v < n
  /-- The input edge is undirected, so reversing its stored endpoint order is allowed. -/
  adjacent : ∀ u v, label v ∈ neighbors edges (label u) ↔ v ∈ neighbors edges u

namespace Automorphism

/-- Apply the automorphism to both endpoints in their traversal order. -/
def dart {n es} (A : Automorphism n es) : Equiv.Perm Edge := A.label.prodCongr A.label

private theorem perm_map_of_mem {α : Type*} (σ : Equiv.Perm α)
    {xs ys : List α} (nx : xs.Nodup) (ny : ys.Nodup)
    (mem : ∀ a, σ a ∈ ys ↔ a ∈ xs) : (xs.map σ).Perm ys := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq (nx.map σ.injective) ny
  ext y
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem a).mpr ha
  · intro hy
    exact ⟨σ.symm y, (mem _).mp (by simpa using hy), σ.apply_symm_apply y⟩

/-- Relabeling both endpoints of every face transports a checked certificate of the same
graph, preserving the order and lengths of all face words. -/
theorem check_map {n edges fs} (A : Automorphism n edges) (G : SimpleInput n edges)
    (hc : check n edges fs = true) : check n edges (fs.map (List.map A.dart)) = true := by
  apply check_iff.mpr
  have cert := check_iff.mp hc
  by_cases iso : n = 1 ∧ edges = []
  · rw [ite_eq_left iso] at cert ⊢
    simp [cert]
  · rw [ite_eq_right iso] at cert ⊢
    obtain ⟨part, r, legal, nd, matchFaces⟩ := cert
    let rows := (List.range n).map fun v => (row r (A.label.symm v)).map A.label
    have get (v : Nat) (hv : v < n) :
        row rows v = (row r (A.label.symm v)).map A.label := by
      simp [rows, row, List.getD_eq_getElem?_getD, hv]
    have invBound (v : Nat) (hv : v < n) : A.label.symm v < n :=
      (A.bounded _).mp (by simpa using hv)
    have adjMap (v : Nat) : ((neighbors edges v).map A.label).Perm
        (neighbors edges (A.label v)) :=
      perm_map_of_mem _ (G.neighbors_nodup _) (G.neighbors_nodup _) (A.adjacent v)
    have univMap : ((Certificate.universe edges).map A.dart).Perm (Certificate.universe edges) := by
      apply perm_map_of_mem _ (universe_nodup G) (universe_nodup G)
      rintro ⟨u,v⟩
      simpa only [mem_universe, mem_neighbors, dart, Equiv.prodCongr_apply, Prod.map_apply,
        Prod.swap_prod_mk] using A.adjacent u v
    refine ⟨⟨?_, ?_⟩, rows, ⟨by simp [rows], ?_⟩, ?_, ?_⟩
    · rw [← List.map_flatten]
      exact (part.1.map A.dart).trans univMap
    · intro f hf
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
      exact ⟨by simpa using (part.2 w hw).1, (part.2 w hw).2.map A.dart.injective⟩
    · intro v hv
      change (row rows v).Perm _
      rw [get v hv]
      exact ((legal.2 _ (invBound _ hv)).map A.label).trans
        (by simpa using adjMap (A.label.symm v))
    · intro v hv
      rw [get v hv]
      exact (nd _ (invBound _ hv)).map A.label.injective
    · intro f hf d hd
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
      obtain ⟨⟨u, v⟩, hmem, rfl⟩ := List.mem_map.mp hd
      have adj := mem_neighbors.mpr (mem_universe.mp
        (part.1.mem_iff.mp (List.mem_flatten.mpr ⟨w, hw, hmem⟩)))
      have hv := G.neighbor_lt (adj : v ∈ neighbors edges u)
      have hu := (legal.2 v hv).mem_iff.mpr (mem_neighbors.mpr (mem_neighbors.mp adj).symm)
      rw [OrbitWords.formPerm_map_apply _ A.dart.injective _ (part.2 w hw).2 _ hmem,
        matchFaces w hw _ hmem]
      refine Prod.ext ?_ ?_
      · rfl
      change A.label ((row r v).formPerm u) = (row rows (A.label v)).formPerm (A.label u)
      rw [get _ ((A.bounded _).mpr hv), A.label.symm_apply_apply,
        OrbitWords.formPerm_map_apply _ A.label.injective _ (nd v hv) _ hu]

/-- An isomorphic root face, stored with any cyclic starting dart, supports a checked
certificate with the same multiset of face lengths, preserving every length layer. -/
theorem replace_root_lengths {n edges fs f g} (A : Automorphism n edges) (G : SimpleInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (root : (f.map A.dart).IsRotated g) :
    ∃ rest, check n edges (g :: rest) = true ∧
      ((g :: rest).map List.length).Perm (fs.map List.length) := by
  let rest := fs.erase f
  have p : fs.Perm (f :: rest) := List.perm_cons_erase hf
  refine ⟨rest.map (List.map A.dart), ?_, ?_⟩
  · have mapped := A.check_map (fs := f :: rest) G (check_perm p hc)
    exact check_rotate (fs := rest.map (List.map A.dart)) root mapped
  · have len : g.length = f.length := by simpa using root.perm.length_eq.symm
    simpa [List.map_map, Function.comp_def, len] using (p.symm.map List.length)

/-- An isomorphic root face, stored with any cyclic starting dart, supports a checked
certificate having the same number of faces. -/
theorem replace_root {n edges fs f g} (A : Automorphism n edges) (G : SimpleInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (root : (f.map A.dart).IsRotated g) :
    ∃ rest, check n edges (g :: rest) = true ∧ (g :: rest).length = fs.length := by
  obtain ⟨rest, good, lengths⟩ := A.replace_root_lengths G hc hf root
  exact ⟨rest, good, by simpa only [List.length_map] using lengths.length_eq⟩

end Automorphism

/-- A retained representative per raw start branch suffices. Each checked solution containing
a raw start transports to one containing the retained representative at the same face count. -/
theorem exists_root_representative {n edges k} (G : SimpleInput n edges)
    (raw kept : Face → Prop)
    (hits : ∀ fs, check n edges fs = true → fs.length = k → ∃ f ∈ fs, raw f)
    (rep : ∀ f, raw f → ∃ g, kept g ∧ ∃ A : Automorphism n edges, (f.map A.dart).IsRotated g) :
    (∃ fs, check n edges fs = true ∧ fs.length = k) ↔
      ∃ g rest, kept g ∧ check n edges (g :: rest) = true ∧ (g :: rest).length = k := by
  constructor
  · rintro ⟨fs, hc, size⟩
    obtain ⟨f, hf, rawf⟩ := hits fs hc size
    obtain ⟨g, keep, A, image⟩ := rep f rawf
    obtain ⟨rest, good, len⟩ := A.replace_root G hc hf image
    exact ⟨g, rest, keep, good, len.trans size⟩
  · rintro ⟨g, rest, _, hc, size⟩
    exact ⟨_, hc, size⟩

end Page.Pruning
