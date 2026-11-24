import BipartiteKneser.Rotation

/-!
# The two-subset graph H(h,2)

An increasing pair represents its two-element subset without multiplicity.
The chart translates the affine dart labels to exactly the neighbors in this graph.
-/

namespace BipartiteKneser

/-- Two distinct points in increasing order. -/
abbrev Pair (h : Nat) := {p : Fin h × Fin h // p.1 < p.2}

/-- A bipartition class and an unordered pair. -/
abbrev Vertex (h : Nat) := Bool × Pair h

/-- Adjacency in H(h,2). -/
def Adj {h : Nat} (v w : Vertex h) : Prop :=
  v.1 ≠ w.1 ∧ BaseCycle.Disjoint v.2.val w.2.val

/-- Reachability by a finite walk in H(h,2). -/
inductive Reachable {h : Nat} (v : Vertex h) : Vertex h → Prop where
  /-- The walk with no edges. -/
  | refl : Reachable v v
  /-- Append an edge to a walk. -/
  | step {w z} : Reachable v w → Adj w z → Reachable v z

private theorem fresh : ∀ a b c d : Fin 6, ∃ i j : Fin 6,
    i < j ∧ i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d ∧ j ≠ a ∧ j ≠ b ∧ j ≠ c ∧ j ≠ d := by
  decide +kernel

private theorem common_pair {h : Nat} (hh : 6 ≤ h) (p r : Pair h) :
    ∃ s : Pair h, BaseCycle.Disjoint p.val s.val ∧ BaseCycle.Disjoint s.val r.val := by
  let reduce (x : Fin h) := Fin.ofNat 6 x.val
  obtain ⟨i, j, hij, hia, hib, hic, hid, hja, hjb, hjc, hjd⟩ :=
    fresh (reduce p.val.1) (reduce p.val.2) (reduce r.val.1) (reduce r.val.2)
  let lift (x : Fin 6) : Fin h := ⟨x.val, Nat.lt_of_lt_of_le x.isLt hh⟩
  have avoid (x : Fin 6) (y : Fin h) (he : x ≠ reduce y) : lift x ≠ y := by
    rintro rfl
    apply he
    exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm
  refine ⟨⟨(lift i, lift j), hij⟩, ?_, ?_⟩
  · exact ⟨(avoid _ _ hia).symm, (avoid _ _ hja).symm,
      (avoid _ _ hib).symm, (avoid _ _ hjb).symm⟩
  · exact ⟨avoid _ _ hic, avoid _ _ hid, avoid _ _ hjc, avoid _ _ hjd⟩

private theorem same_side {h : Nat} (hh : 6 ≤ h) (b : Bool) (p r : Pair h) :
    Reachable (b, p) (b, r) := by
  obtain ⟨s, hp, hr⟩ := common_pair hh p r
  have flip : b ≠ !b := by cases b <;> decide
  exact .step (.step .refl (show Adj (b, p) (!b, s) from ⟨flip, hp⟩)) ⟨flip.symm, hr⟩

/-- H(h,2) is connected when h ≥ 6. Vertices on the same side have a
common neighbor and any vertex on the opposite side has a neighbor. -/
theorem connected {h : Nat} (hh : 6 ≤ h) (v w : Vertex h) : Reachable v w := by
  obtain ⟨b, p⟩ := v
  obtain ⟨t, r⟩ := w
  by_cases eq : b = t
  · subst t
    exact same_side hh b p r
  · obtain ⟨s, _, hs⟩ := common_pair hh r r
    exact .step (same_side hh b p s) ⟨eq, hs⟩

namespace BaseCycle

variable {h q d : Nat} {c : BaseCycle h q d}

/-- The actual two-subset vertex represented by a framed vertex. -/
def Chart.vertex (ch : c.Chart) (part : Bool) (g : Frame h q) : Vertex h :=
  (part, ⟨c.sortedPoints g, ch.increasing g⟩)

/-- The chart covers both entire bipartition classes. -/
theorem Chart.onto (ch : c.Chart) (v : Vertex h) :
    ch.vertex v.1 (ch.decode v.2.val.1 v.2.val.2) = v := by
  obtain ⟨b, ⟨⟨a, z⟩, haz⟩⟩ := v
  simp [Chart.vertex, ch.rightInv _ _ haz]

/-- A framed vertex has a unique two-subset label in its class. -/
theorem Chart.injective (ch : c.Chart) (b t : Bool) (g s : Frame h q)
    (he : ch.vertex b g = ch.vertex t s) : b = t ∧ g = s := by
  have hs := congrArg (fun v : Vertex h => v.2.val) he
  exact ⟨congrArg Prod.fst he, (ch.leftInv g).symm.trans
    ((congrArg (fun p => ch.decode p.1 p.2) hs).trans (ch.leftInv s))⟩

/-- A dart from the affine rotation is exactly an edge in the two-subset graph. -/
theorem Chart.adj_iff [NeZero h] [NeZero q] (ch : c.Chart) (pw : c.Powers) (cv : c.Covers)
    (b t : Bool) (g s : Frame h q) :
    Adj (ch.vertex b g) (ch.vertex t s) ↔ b ≠ t ∧ ∃ i, compose c.scale g (c.label i) = s := by
  unfold Adj Chart.vertex
  simp only [c.adjacency_iff pw cv g s |>.symm]
  unfold sortedPoints
  split
  split <;> simp [Disjoint] <;> grind

end BaseCycle
end BipartiteKneser
