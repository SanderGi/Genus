/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Representation
import Page.Certificate

/-! # Identifying the roots of two vertex-labeled graphs -/

@[expose] public section

namespace HoG.VertexSum

open MultiGenus MultiGenus.Rotations MultiGenus.Faces

/-- Number of vertices after identifying the two vertices labeled zero. -/
def vertices (nL nR : Nat) := nL + (nR - 1)

/-- Keep the right root at zero and place the other right labels after the left vertices. -/
def rightLabel (nL : Nat) : Nat → Nat
  | 0 => 0
  | v + 1 => nL + v

/-- Apply the right-side label change to a pair of endpoints. -/
def rightEdge (nL : Nat) : Edge → Edge := Prod.map (rightLabel nL) (rightLabel nL)

/-- Retain left edges and append the relabeled right edges in input order. -/
def edges (nL : Nat) (esL esR : List Edge) := esL ++ esR.map (rightEdge nL)

@[simp] theorem length_edges (nL : Nat) (esL esR : List Edge) :
    (edges nL esL esR).length = esL.length + esR.length := by simp [edges]

theorem vertices_eq {nL nR : Nat} (hR : 0 < nR) : vertices nL nR = nL + nR - 1 := by
  unfold vertices
  omega

/-- Right labels increase strictly when the left graph contains its root. -/
theorem strict {nL : Nat} (hL : 0 < nL) : StrictMono (rightLabel nL) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightLabel]

private theorem bounds {nL nR v : Nat} (hL : 0 < nL) (hv : v < nR) :
    rightLabel nL v < vertices nL nR := by cases v <;> simp [vertices, rightLabel] <;> omega

private theorem right_large {nL v : Nat} (pos : 0 < v) : nL ≤ rightLabel nL v := by
  cases v <;> simp_all [rightLabel]

/-- Left and right edge inventories are disjoint since each right edge has a positive
larger endpoint. The order of each edge is preserved. -/
theorem simple {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) : SimpleInput (vertices nL nR) (edges nL esL esR) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with hl | hr
    · exact GL.ordered e hl
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      exact strict hL (GR.ordered d hd)
  · intro e he
    rcases List.mem_append.mp he with hl | hr
    · exact (GL.bounded e hl).trans_le (Nat.le_add_right ..)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      exact bounds hL (GR.bounded d hd)
  · apply List.nodup_append.mpr
    refine ⟨GL.nodup, GR.nodup.map (Prod.map_injective.mpr ⟨(strict hL).injective,
      (strict hL).injective⟩), ?_⟩
    rintro e he _ hm rfl
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
    have lt := GL.bounded _ he
    have ge := right_large (nL := nL) (Nat.zero_lt_of_lt (GR.ordered d hd))
    exact (Nat.not_le_of_gt lt) ge

private theorem left_adj {nL esL esR u v} (h : v ∈ neighbors esL u) :
    v ∈ neighbors (edges nL esL esR) u :=
  mem_neighbors.mpr ((mem_neighbors.mp h).imp (List.mem_append_left _) (List.mem_append_left _))

private theorem right_adj {nL esL esR u v} (h : v ∈ neighbors esR u) :
    rightLabel nL v ∈ neighbors (edges nL esL esR) (rightLabel nL u) := by
  apply mem_neighbors.mpr
  exact (mem_neighbors.mp h).imp (fun e => List.mem_append_right _ (List.mem_map_of_mem
    (f := rightEdge nL) e)) (fun e => List.mem_append_right _ (List.mem_map_of_mem
    (f := rightEdge nL) e))

/-- Paths inside either summand lead to the same root in the combined graph. -/
theorem connected {nL nR esL esR} (cL : ConnectedInput nL esL) (cR : ConnectedInput nR esR) :
    ConnectedInput (vertices nL nR) (edges nL esL esR) := by
  let adj (u v : Nat) := v ∈ neighbors (edges nL esL esR) u
  have reach (z : Nat) (hz : z < vertices nL nR) : Relation.ReflTransGen adj 0 z := by
    by_cases left : z < nL
    · exact (cL.2 0 cL.1 z left).lift id (fun _ _ h => left_adj h)
    · let w := z - nL
      have hw : w + 1 < nR := by unfold vertices at hz; dsimp [w]; omega
      have path := (cR.2 0 cR.1 _ hw).lift (rightLabel nL) (p := adj) (fun _ _ h => right_adj h)
      have eq : rightLabel nL (w + 1) = z := by simp [rightLabel, w]; omega
      exact eq ▸ path
  refine ⟨Nat.lt_of_lt_of_le cL.1 (Nat.le_add_right ..), fun u hu v hv => ?_⟩
  have back : Relation.ReflTransGen adj u 0 := by
    have path := reach u hu
    clear hu
    induction path with
    | refl => exact .refl
    | tail _ h ih => exact ih.head (mem_neighbors.mpr (mem_neighbors.mp h).symm)
  exact back.trans (reach v hv)

/-- Canonical incidence rows in input edge order. -/
def rows (n : Nat) (es : List Edge) := (List.range n).map (neighbors es)

theorem legal (n : Nat) (es : List Edge) : Legal n es (rows n es) :=
  (mem_enumerate_iff ..).mp (adjacency_mem_enumerate n es)

private theorem mem_darts_iff {n es} (G : SimpleInput n es) (d : Edge) :
    d ∈ darts (rows n es) ↔ d ∈ es ∨ d.swap ∈ es := by
  rcases d with ⟨u,v⟩
  have h := legal n es
  constructor
  · intro hd
    obtain ⟨hu, hv⟩ := mem_darts.mp hd
    exact mem_neighbors.mp ((h.2 u (h.1 ▸ hu)).mem_iff.mp hv)
  · intro hd
    have hv := mem_neighbors.mpr hd
    have hu := G.neighbor_lt (mem_neighbors.mpr hd.symm)
    exact mem_darts.mpr ⟨by rw [h.1]; exact hu, (h.2 u hu).mem_iff.mpr hv⟩

/-- Every combined dart comes from an input edge in one of the two components. -/
theorem mem_sum {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (d : Edge) :
    d ∈ darts (rows (vertices nL nR) (edges nL esL esR)) ↔
      d ∈ darts (rows nL esL) ∨ ∃ y ∈ darts (rows nR esR), rightEdge nL y = d := by
  rw [mem_darts_iff (simple GL GR hL), mem_darts_iff GL]
  simp only [edges, List.mem_append, List.mem_map]
  constructor
  · rintro ((hl | ⟨y, hy, eq⟩) | (hl | ⟨y, hy, eq⟩))
    · exact .inl (.inl hl)
    · exact .inr ⟨y, (mem_darts_iff GR _).mpr (.inl hy), eq⟩
    · exact .inl (.inr hl)
    · exact .inr ⟨y.swap, (mem_darts_iff GR _).mpr (.inr hy), congrArg Prod.swap eq⟩
  · rintro (hl | ⟨y, hy, rfl⟩)
    · exact hl.elim (Or.inl ∘ Or.inl) (Or.inr ∘ Or.inl)
    · rcases (mem_darts_iff GR y).mp hy with hy | hy
      · exact .inl (.inr ⟨y, hy, rfl⟩)
      · exact .inr (.inr ⟨y.swap, hy, rfl⟩)

/-- The dart carrier in canonical neighbor rows. -/
abbrev Darts (n : Nat) (es : List Edge) := Dart (rows n es)

/-- Reversal of a canonical dart. -/
def rev {n es} (G : SimpleInput n es) : Equiv.Perm (Darts n es) :=
  alpha (valid_of_legal G (legal ..))

private theorem ends_lt {n es} (G : SimpleInput n es) (d : Darts n es) :
    d.val.1 < n ∧ d.val.2 < n := by
  have adj := (mem_darts_iff G d.val).mp d.prop
  exact ⟨G.neighbor_lt (mem_neighbors.mpr adj.symm), G.neighbor_lt (mem_neighbors.mpr adj)⟩

/-- No oriented edge of the right summand is identified with an edge on the left. -/
theorem disjoint_image {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (x : Darts nL esL) (y : Darts nR esR) : x.val ≠ rightEdge nL y.val := by
  intro eq
  have ⟨l, r⟩ := ends_lt GL x
  rw [eq] at l r
  rcases (mem_darts_iff GR _).mp y.prop with h | h
  · exact (Nat.not_le_of_gt r) (right_large (Nat.zero_lt_of_lt (GR.ordered _ h)))
  · exact (Nat.not_le_of_gt l) (right_large (Nat.zero_lt_of_lt (GR.ordered _ h)))

/-- Gluing at a vertex preserves both copies of every directed edge. -/
noncomputable def dartEquiv {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) :
    Darts nL esL ⊕ Darts nR esR ≃ Darts (vertices nL nR) (edges nL esL esR) := by
  let left (x : Darts nL esL) : Darts (vertices nL nR) (edges nL esL esR) :=
    ⟨x.val, (mem_sum GL GR hL _).mpr (.inl x.prop)⟩
  let right (x : Darts nR esR) : Darts (vertices nL nR) (edges nL esL esR) :=
    ⟨rightEdge nL x.val, (mem_sum GL GR hL _).mpr (.inr ⟨_, x.prop, rfl⟩)⟩
  let endpoints (d : Darts (vertices nL nR) (edges nL esL esR)) := d.val
  refine Equiv.ofBijective (Sum.elim left right) ⟨?_, ?_⟩
  · rintro (x | x) (y | y) eq
    · exact congrArg Sum.inl (Subtype.ext (congrArg endpoints eq))
    · exact (disjoint_image GL GR x y (congrArg endpoints eq)).elim
    · exact (disjoint_image GL GR y x (congrArg endpoints eq.symm)).elim
    · have inj : Function.Injective (rightEdge nL) :=
        Prod.map_injective.mpr ⟨(strict hL).injective, (strict hL).injective⟩
      exact congrArg Sum.inr (Subtype.ext (inj (congrArg endpoints eq)))
  · intro d
    rcases (mem_sum GL GR hL _).mp d.prop with left | ⟨y, hy, eq⟩
    · exact ⟨.inl ⟨_, left⟩, Subtype.ext rfl⟩
    · exact ⟨.inr ⟨y, hy⟩, Subtype.ext eq⟩

@[simp] theorem dartEquiv_inl {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x : Darts nL esL) : (dartEquiv GL GR hL (.inl x)).val = x.val := rfl

@[simp] theorem dartEquiv_inr {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x : Darts nR esR) :
    (dartEquiv GL GR hL (.inr x)).val = rightEdge nL x.val := rfl

/-- The concrete equivalence commutes with the separate dart reversals. -/
theorem reverse {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x : Darts nL esL ⊕ Darts nR esR) :
    dartEquiv GL GR hL (((rev GL).sumCongr (rev GR)) x) =
      rev (simple GL GR hL) (dartEquiv GL GR hL x) := by
  cases x <;> exact Subtype.ext rfl

/-- An origin from either component is untagged at zero; all other origins retain their side. -/
def originTag {nL nR esL esR} : Darts nL esL ⊕ Darts nR esR → Option (Nat ⊕ Nat)
  | .inl d => if d.val.1 = 0 then none else some (.inl d.val.1)
  | .inr d => if d.val.1 = 0 then none else some (.inr d.val.1)

private theorem cross {nL a b : Nat} (ha : a < nL) :
    a = rightLabel nL b ↔ a = 0 ∧ b = 0 := by cases b <;> simp [rightLabel]; omega

/-- Concrete origins coincide exactly for the fibers used by abstract vertex gluing. -/
theorem origins {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (hL : 0 < nL) (x y : Darts nL esL ⊕ Darts nR esR) :
    originTag x = originTag y ↔ (dartEquiv GL GR hL x).val.1 = (dartEquiv GL GR hL y).val.1 := by
  cases x with
  | inl x =>
    cases y with
    | inl y => simp [originTag]; split_ifs <;> grind
    | inr y =>
      change _ ↔ x.val.1 = rightLabel nL y.val.1
      rw [cross (ends_lt GL x).1]
      simp only [originTag]
      split_ifs <;> grind
  | inr x =>
    cases y with
    | inl y =>
      change _ ↔ rightLabel nL x.val.1 = y.val.1
      rw [@eq_comm _ (rightLabel nL x.val.1) y.val.1, cross (ends_lt GL y).1]
      simp only [originTag]
      split_ifs <;> grind
    | inr y =>
      change _ ↔ rightLabel nL x.val.1 = rightLabel nL y.val.1
      rw [(strict hL).injective.eq_iff]
      simp only [originTag]
      split_ifs <;> grind

/-- For the concrete vertex sum, every abstract genus on the disjoint dart carriers
is attained by legal rows of the combined graph, and conversely. -/
theorem attains_iff_realizes {nL nR esL esR} (GL : SimpleInput nL esL) (GR : SimpleInput nR esR)
    (cL : ConnectedInput nL esL) (cR : ConnectedInput nR esR)
    (hn : 1 < vertices nL nR) (g : Nat) :
    Reduction.Attains (vertices nL nR) (esL.length + esR.length)
      (@originTag nL nR esL esR) ((rev GL).sumCongr (rev GR)) g ↔
      Realizes (vertices nL nR) (edges nL esL esR) g := by
  let e := dartEquiv GL GR cL.1
  let H := simple GL GR cL.1
  rw [← Representation.attains_iff_realizes H (connected cL cR) (legal ..) hn,
    length_edges]
  constructor
  · exact Representation.attains_of_equiv e (origins GL GR cL.1) (reverse GL GR cL.1)
  · apply Representation.attains_of_equiv e.symm
    · intro x y
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      simpa only [e.symm_apply_apply] using (origins GL GR cL.1 x y).symm
    · intro x
      obtain ⟨x, rfl⟩ := e.surjective x
      rw [e.symm_apply_apply]
      exact e.symm_apply_eq.mpr (reverse GL GR cL.1 x).symm

/-- A dart in the canonical rows is precisely an undirected adjacency with a chosen source. -/
theorem dart_iff_adj {n es} (G : SimpleInput n es) (u v : Nat) :
    (u, v) ∈ darts (rows n es) ↔ v ∈ neighbors es u := (mem_darts_iff G _).trans mem_neighbors.symm

private theorem dartCard {n es} (G : SimpleInput n es) :
    Fintype.card (Darts n es) = 2 * es.length := by
  have eq : darts (rows n es) = (Page.Certificate.universe es).toFinset := by
    ext d
    rw [List.mem_toFinset, Page.Certificate.mem_universe, mem_darts_iff G]
  rw [Fintype.card_coe, eq, List.toFinset_card_of_nodup (Page.Certificate.universe_nodup G)]
  simp [Page.Certificate.universe, two_mul]

/-- Relabeling vertices on both ends identifies the concrete darts, independently of how
the undirected input edges were oriented for storage or ordered in the input list. -/
def relabelDarts {n m es fs} (G : SimpleInput n es) (H : SimpleInput m fs) (σ : Equiv.Perm Nat)
    (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u) : Darts n es ≃ Darts m fs :=
  (σ.prodCongr σ).subtypeEquiv (fun ⟨u,v⟩ => (dart_iff_adj G u v).trans
    ((adj u v).symm.trans (dart_iff_adj H _ _).symm))

/-- Relabeling preserves the origin fibers used in the row representation theorem. -/
theorem relabel_origins {n m es fs} (G : SimpleInput n es) (H : SimpleInput m fs)
    (σ : Equiv.Perm Nat) (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u)
    (x y : Darts n es) :
    x.val.1 = y.val.1 ↔ (relabelDarts G H σ adj x).val.1 = (relabelDarts G H σ adj y).val.1 :=
  σ.injective.eq_iff.symm

/-- Relabeling leaves reversal equivariant. -/
theorem relabel_reverse {n m es fs} (G : SimpleInput n es) (H : SimpleInput m fs)
    (σ : Equiv.Perm Nat) (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u)
    (x : Darts n es) : relabelDarts G H σ adj (rev G x) = rev H (relabelDarts G H σ adj x) :=
  Subtype.ext rfl

/-- A relabeling preserving adjacency preserves the input edge count. -/
theorem length_relabel {n m es fs} (G : SimpleInput n es) (H : SimpleInput m fs)
    (σ : Equiv.Perm Nat) (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u) :
    es.length = fs.length := by
  have eq := Fintype.card_congr (relabelDarts G H σ adj)
  rw [dartCard G, dartCard H] at eq
  omega

private theorem realizes_map {n es fs g} (G : SimpleInput n es) (H : SimpleInput n fs)
    (cG : ConnectedInput n es) (cH : ConnectedInput n fs) (hn : 1 < n) (σ : Equiv.Perm Nat)
    (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u) (h : Realizes n es g) :
    Realizes n fs g := by
  have src := (Representation.attains_iff_realizes G cG (legal n es) hn g).mpr h
  apply (Representation.attains_iff_realizes H cH (legal n fs) hn g).mp
  rw [← length_relabel G H σ adj]
  exact Representation.attains_of_equiv (relabelDarts G H σ adj) (relabel_origins G H σ adj)
    (relabel_reverse G H σ adj) src

/-- Vertex relabeling preserves the public minimum, including the isolated root graph. -/
theorem minimumGenus_relabel {n es fs} (G : SimpleInput n es) (H : SimpleInput n fs)
    (cG : ConnectedInput n es) (cH : ConnectedInput n fs) (σ : Equiv.Perm Nat)
    (adj : ∀ u v, σ v ∈ neighbors fs (σ u) ↔ v ∈ neighbors es u) :
    minimumGenus n es = minimumGenus n fs := by
  by_cases hn : 1 < n
  · have back (u v : Nat) : σ.symm v ∈ neighbors es (σ.symm u) ↔ v ∈ neighbors fs u := by
      simpa only [σ.apply_symm_apply] using (adj (σ.symm u) (σ.symm v)).symm
    exact le_antisymm
      ((minimumGenus_isLeast G cG).2 (realizes_map H G cH cG hn σ.symm back
        (minimumGenus_isLeast H cH).1))
      ((minimumGenus_isLeast H cH).2 (realizes_map G H cG cH hn σ adj
        (minimumGenus_isLeast G cG).1))
  · have empty {l} (S : SimpleInput n l) : l = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hd
      have := S.ordered d hd
      have := S.bounded d hd
      omega
    rw [empty G, empty H]

/-- Finite label bijections as produced by the concrete split checker preserve the minimum.
The equality of vertex counts follows from the bijection itself. -/
theorem minimumGenus_relabel_fin {k n es fs} (G : SimpleInput k es) (H : SimpleInput n fs)
    (cG : ConnectedInput k es) (cH : ConnectedInput n fs) (e : Fin k ≃ Fin n)
    (adj : ∀ u v, v.val ∈ neighbors es u.val ↔ (e v).val ∈ neighbors fs (e u).val) :
    minimumGenus k es = minimumGenus n fs := by
  have eq : k = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  let perm : Equiv.Perm (Fin k) := e
  let σ := perm.extendDomain Fin.equivSubtype
  have inside (x : Fin k) : σ x.val = (e x).val :=
    perm.extendDomain_apply_image Fin.equivSubtype x
  have outside {x : Nat} (h : ¬x < k) : σ x = x :=
    perm.extendDomain_apply_not_subtype Fin.equivSubtype h
  apply minimumGenus_relabel G H cG cH σ
  intro u v
  by_cases hu : u < k
  · by_cases hv : v < k
    · rw [inside ⟨u, hu⟩, inside ⟨v, hv⟩]
      exact (adj ⟨u, hu⟩ ⟨v, hv⟩).symm
    · rw [outside hv]
      exact ⟨fun h => (hv (H.neighbor_lt h)).elim, fun h => (hv (G.neighbor_lt h)).elim⟩
  · rw [outside hu]
    exact ⟨fun h => (hu (H.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp h).symm))).elim,
      fun h => (hu (G.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp h).symm))).elim⟩

end HoG.VertexSum
