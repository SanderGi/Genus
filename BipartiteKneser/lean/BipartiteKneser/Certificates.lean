import BipartiteKneser.Rotation

/-!
# Certificate interface for the exceptional primes (Section 8)

A witness includes a chart onto all two-subsets, a complete local rotation,
and the quadrilateral equations. The finite checks on the base cycle imply
the assertions about darts and vertices by the theorems in `Rotation`.
-/

namespace BipartiteKneser

/-- Read a fixed-width unsigned entry from a packed table, least significant first. -/
def entry (table bits i : Nat) : Nat := (table >>> (bits * i)) % (2 ^ bits)

/-- Unpack a cycle and its inverse lookup; the certificate theorems check both. -/
def unpack {h q d : Nat} [NeZero h] [NeZero q] [NeZero d]
    (bits powers labels indices : Nat) : BaseCycle h q d where
  scale k := Fin.ofNat h (entry powers bits k.val)
  label i :=
    let code := entry labels bits i.val
    (Fin.ofNat h (code / q), Fin.ofNat q (code % q))
  index s := Fin.ofNat d (entry indices bits (s.1.val * q + s.2.val))

/-- Decode an increasing two-subset using the signed discrete logarithm of its difference. -/
def decodePair {h q : Nat} [NeZero h] [NeZero q]
    (bits logs : Nat) (a b : Fin h) : Frame h q :=
  let code := entry logs bits (b - a).val
  (if code < q then a else b, Fin.ofNat q code)

/-- The combinatorial existence assertion for a vertex-transitive orientable
quadrangulation in the affine model. The chart identifies its vertices with
the two classes of two-subsets. Every facial orbit has four distinct corners. -/
def HasAffineQuadrangulation (h q d : Nat) [NeZero h] [NeZero q] [NeZero d] : Prop :=
  ∃ c : BaseCycle h q d, Nonempty c.Chart ∧ c.Powers ∧ c.Covers ∧
    (∀ x, c.reverse (c.reverse x) = x) ∧
    (∀ x, c.face (c.face (c.face (c.face x))) = x ∧
      (c.face (c.face x)).2.1 ≠ x.2.1 ∧
      (c.face (c.face (c.face x))).2.1 ≠ (c.face x).2.1) ∧
    c.VertexTransitive

/-- Lift the checks at the base labels to all darts of the disjoint-pair graph. -/
theorem of_certificate {h q d : Nat} [NeZero h] [NeZero q] [NeZero d]
    (c : BaseCycle h q d) (ch : c.Chart) (pw : c.Powers) (cv : c.Covers)
    (ok : ∀ p i, c.checkFace p i = true) : HasAffineQuadrangulation h q d :=
  ⟨c, ⟨ch⟩, pw, cv, c.reverse_reverse pw cv, c.quadrilateral pw ok, c.vertex_transitive pw⟩

end BipartiteKneser
