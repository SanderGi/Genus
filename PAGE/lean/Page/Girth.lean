/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.FaceBounds
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # Girth, parity and return-distance pruning of rooted facial walks -/

@[expose] public section

namespace Page.Girth

open MultiGenus MultiGenus.Rotations Page.Certificate SimpleGraph

/-- The input adjacency relation on vertex labels. Labels outside the input range are isolated. -/
def graph {n edges} (G : SimpleInput n edges) : SimpleGraph Nat where
  Adj a b := b ∈ neighbors edges a
  symm := ⟨fun _ _ h => mem_neighbors.mpr (mem_neighbors.mp h).symm⟩
  loopless := ⟨fun a h => (mem_neighbors.mp h).elim
    (fun e => (Nat.lt_irrefl a) (G.ordered _ e)) (fun e => (Nat.lt_irrefl a) (G.ordered _ e))⟩

variable {V : Type*} {H : SimpleGraph V}

/-- The directed endpoint pairs traversed by a mathlib walk, in their traversal order. -/
def pairs {u v : V} : H.Walk u v → List (V × V)
  | .nil => []
  | @Walk.cons _ _ a b _ _ tail => (a, b) :: pairs tail

@[simp] theorem length_pairs {u v : V} (p : H.Walk u v) : (pairs p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [pairs, ih]

private theorem origin_getElem {u v : V} (p : H.Walk u v) (i : Nat) (hi : i < (pairs p).length) :
    (pairs p)[i].1 = p.getVert i := by
  induction p generalizing i with
  | nil => simp at hi
  | cons h q ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

private theorem walk_of_chain {n edges} (G : SimpleInput n edges) (d last : Edge) (ds : List Edge)
    (onGraph : ∀ x ∈ d :: ds, (graph G).Adj x.1 x.2)
    (chain : (d :: ds ++ [last]).IsChain Walks.Fits) :
    ∃ p : (graph G).Walk d.1 last.1, pairs p = d :: ds := by
  induction ds generalizing d with
  | nil =>
    have eq : d.2 = last.1 := chain.rel
    have adj := onGraph d (.head _)
    refine ⟨.cons (eq ▸ adj) .nil, ?_⟩
    simp [pairs, ← eq]
  | cons e ds ih =>
    obtain ⟨q, hq⟩ := ih e (fun x hx => onGraph x (.tail _ hx)) chain.tail
    have eq : d.2 = e.1 := chain.rel
    have adj := onGraph d (.head _)
    refine ⟨.cons (eq ▸ adj) q, ?_⟩
    simp [pairs, hq, ← eq]

/-- Each checked face is a closed walk of the input graph with exactly the listed darts. -/
theorem exists_walk_of_check {n edges fs f} (G : SimpleInput n edges) (hc : check n edges fs = true)
    (hf : f ∈ fs) : ∃ a, ∃ p : (graph G).Walk a a, pairs p = f := by
  cases f with
  | nil => exact ⟨0, .nil, rfl⟩
  | cons d ds =>
    have sub (x : Edge) (hx : x ∈ d :: ds) : x ∈ Certificate.universe edges :=
      (check_flatten_perm hc).mem_iff.mp (List.mem_flatten.mpr ⟨_, hf, hx⟩)
    have he : edges ≠ [] := by
      rintro rfl
      have hm := sub d (.head _)
      simp [Certificate.universe] at hm
    have chain := (admissible_of_check he hc hf).2.2.2
    exact ⟨d.1, walk_of_chain G d d ds (fun x hx =>
      mem_neighbors.mpr (mem_universe.mp (sub x hx))) chain⟩

private theorem two_le_takeUntil [DecidableEq V] {a b c : V} (h : H.Adj a b) (p : H.Walk b c)
    (mem : a ∈ p.support) (straight : (pairs (p.cons h)).IsChain (fun x y => y ≠ x.swap)) :
    2 ≤ (p.takeUntil a mem).length := by
  classical
  have atEnd := p.getVert_length_takeUntil mem
  cases p with
  | nil =>
    have eq : a = b := Walk.mem_support_nil_iff.mp mem
    exact (h.ne eq).elim
  | @cons _ d _ hb q =>
    have neq : d ≠ a := fun e => straight.rel (Prod.ext rfl e)
    by_contra! short
    have cases : ((q.cons hb).takeUntil a mem).length = 0 ∨
        ((q.cons hb).takeUntil a mem).length = 1 := by omega
    rcases cases with len | len
    · rw [len, Walk.getVert_zero] at atEnd
      exact h.ne atEnd.symm
    · rw [len] at atEnd
      exact neq (by simpa only [Walk.getVert_cons_succ, Walk.getVert_zero] using atEnd)

/-- A nonbacktracking walk either has no repeated vertex or contains a contiguous simple cycle. -/
theorem path_or_cycle {a b : V} (p : H.Walk a b)
    (straight : (pairs p).IsChain (fun x y => y ≠ x.swap)) :
    p.IsPath ∨ ∃ v, ∃ q : H.Walk v v, q.IsCycle ∧ q.IsSubwalk p := by
  classical
  induction p with
  | nil => exact Or.inl Walk.IsPath.nil
  | @cons a b c h p ih =>
    rcases ih straight.tail with path | ⟨v, q, cycle, sub⟩
    · by_cases mem : a ∈ p.support
      · let t := p.takeUntil a mem
        refine Or.inr ⟨a, t.cons h, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [Walk.tail_cons]
          exact (Walk.isPath_copy ..).mpr (path.takeUntil mem)
        · exact Nat.succ_le_succ (two_le_takeUntil h p mem straight)
        · rw [Walk.isSubwalk_iff_support_isInfix, Walk.support_cons, Walk.support_cons]
          exact ((List.prefix_cons_inj a).mpr (p.support_takeUntil_prefix_support mem)).isInfix
      · exact Or.inl (path.cons mem)
    · exact Or.inr ⟨v, q, cycle, sub.cons h⟩

/-- No incoming dart is followed by its reverse, including the turn across the cyclic cut. -/
def NoReversal (f : Face) : Prop := ∀ d ∈ f, f.formPerm d ≠ d.swap

private theorem linear_noReversal {f : Face} (nd : f.Nodup) (h : NoReversal f) :
    f.IsChain (fun x y => y ≠ x.swap) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  simpa only [List.formPerm_apply_lt_getElem f nd i hi] using
    h f[i] (List.getElem_mem (by omega))

/-- A nonempty facial walk without a U-turn is at least as long as the ordinary graph girth. -/
private theorem girth_le_nonempty_face {n edges fs f} (G : SimpleInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (ne : f ≠ []) (straight : NoReversal f) :
    (graph G).girth ≤ f.length := by
  have he : edges ≠ [] := by
    rintro rfl
    obtain ⟨d, hd⟩ := f.exists_mem_of_ne_nil ne
    have mem := (check_flatten_perm hc).mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, hd⟩)
    simp [Certificate.universe] at mem
  obtain ⟨a, p, eq⟩ := exists_walk_of_check G hc hf
  have h := linear_noReversal (check_face he hc hf).2.1 straight
  rw [← eq] at h
  rcases path_or_cycle p h with path | ⟨v, q, cycle, sub⟩
  · have nil := (Walk.isPath_iff_nil.mp path).eq_nil
    exact (ne (eq.symm.trans (nil ▸ rfl))).elim
  · have le := (Walk.isSubwalk_iff_support_isInfix.mp sub).length_le
    simp only [Walk.length_support, Nat.add_le_add_iff_right] at le
    rw [← eq, length_pairs]
    exact cycle.girth_le_length.trans le

/-- Girth bounds every checked face without a reversing turn, including the empty face of K1. -/
theorem girth_le_face {n edges fs f} (G : SimpleInput n edges) (hc : check n edges fs = true)
    (hf : f ∈ fs) (straight : NoReversal f) : (graph G).girth ≤ f.length := by
  by_cases ne : f ≠ []
  · exact girth_le_nonempty_face G hc hf ne straight
  · have good := check_iff.mp hc
    split at good
    · rename_i iso
      obtain ⟨rfl, rfl⟩ := iso
      have empty : graph G = ⊥ := by ext u v; simp [graph, neighbors]
      simp [empty]
    · exact (ne ((good.1.2 f hf).1)).elim

/-- Every actual edge remains connected between its endpoints after that edge is deleted. -/
def Bridgeless (H : SimpleGraph V) : Prop := ∀ a b, H.Adj a b → ¬ H.IsBridge s(a, b)

private theorem bridge_of_leaf {a b : V} (adj : H.Adj a b) (only : ∀ v, H.Adj a v → v = b) :
    H.IsBridge s(a, b) := by
  apply isBridge_iff.mpr
  rintro ⟨p⟩
  cases p with
  | nil => exact adj.ne rfl
  | cons h _ =>
    obtain ⟨edge, absent⟩ := deleteEdges_adj.mp h
    exact absent (by simp [only _ edge])

/-- A bridge-free graph has no reversing turn in any certified face. -/
theorem noReversal_of_bridgeless {n edges fs f} (G : SimpleInput n edges)
    (free : Bridgeless (graph G)) (hc : check n edges fs = true) (hf : f ∈ fs) : NoReversal f := by
  rintro ⟨u, v⟩ hd rev
  have deg := (FaceBounds.reverses_iff_leaf G hc hf hd).mp rev
  obtain ⟨w, row⟩ := List.length_eq_one_iff.mp deg
  have forward : v ∈ neighbors edges u := mem_neighbors.mpr (mem_universe.mp
    ((check_flatten_perm hc).mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, hd⟩)))
  have back : (graph G).Adj v u := (show (graph G).Adj u v from forward).symm
  have eq : u = w := by simpa only [graph, row, List.mem_singleton] using back
  refine free v u back (bridge_of_leaf back fun x hx => ?_)
  simpa only [graph, row, List.mem_singleton, eq] using hx

/-- On a bridgeless input the native search may start every face at the graph girth. -/
theorem girth_le_of_bridgeless {n edges fs f} (G : SimpleInput n edges)
    (free : Bridgeless (graph G)) (hc : check n edges fs = true) (hf : f ∈ fs) :
    (graph G).girth ≤ f.length :=
  girth_le_face G hc hf (noReversal_of_bridgeless G free hc hf)

/-- Bipartite face searches may skip every odd length, even when the walk repeats vertices. -/
theorem even_face_of_bipartite {n edges fs f} (G : SimpleInput n edges)
    (bip : (graph G).IsBipartite) (hc : check n edges fs = true) (hf : f ∈ fs) : Even f.length := by
  obtain ⟨a, p, rfl⟩ := exists_walk_of_check G hc hf
  rw [length_pairs]
  exact isBipartite_iff_forall_walk_even_length.mp bip a p

/-- A proposed return segment of bounded length is impossible if its distance exceeds the budget.
Extended distance also covers an unreachable home vertex. -/
theorem no_return_of_distance {u home : V} {remaining : Nat} (far : remaining < H.edist u home) :
    ¬ ∃ p : H.Walk u home, p.length ≤ remaining := by
  rintro ⟨p, fits⟩
  exact far.not_ge (p.edist_le.trans (by exact_mod_cast fits))

/-- After the first `k` darts, the remaining part of any certified face must reach its root. -/
theorem distance_home_le_remaining {n edges fs f} (G : SimpleInput n edges)
    (hc : check n edges fs = true) (hf : f ∈ fs) (k : Nat) (hk : k < f.length) :
    (graph G).dist f[k].1 (f[0]'(by omega)).1 ≤ f.length - k := by
  obtain ⟨a, p, rfl⟩ := exists_walk_of_check G hc hf
  rw [origin_getElem p k hk, origin_getElem p 0 _, Walk.getVert_zero, length_pairs]
  simpa using dist_le (p.drop k)

end Page.Girth
