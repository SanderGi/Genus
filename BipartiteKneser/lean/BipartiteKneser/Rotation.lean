module

public import Std

/-!
# Facial walks in affine coordinates

A frame with origin c and exponent k labels the unordered pair {c, c + u^k}.
Both parts use outward labels: the head of dart (g,i) has frame g * sᵢ.
Reversing a dart inverts its label. The B rotation runs backwards through
the same base cycle, as in the paper's expanded rotation convention.
-/

@[expose] public section

set_option linter.all true

namespace BipartiteKneser

/-- Affine frame (translation, exponent) over the residues modulo h and q. -/
abbrev Frame (h q : Nat) := Fin h × Fin q

variable {h q d : Nat}

/-- Affine composition with the given table of multipliers. -/
def compose (u : Fin q → Fin h) (g s : Frame h q) : Frame h q :=
  (g.1 + u g.2 * s.1, g.2 + s.2)

/-- Definition 2.1. The image of {0,1} misses {0,1}. -/
def separated [NeZero h] (u : Fin q → Fin h) (s : Frame h q) : Bool :=
  let endpoint := s.1 + u s.2
  s.1 != 0 && s.1 != 1 && endpoint != 0 && endpoint != 1

/-- A cyclic list of affine frames, indexed modulo its length. -/
structure BaseCycle (h q d : Nat) where
  /-- Multiplier at each exponent. -/
  scale : Fin q → Fin h
  /-- Outward label at a position of the cycle. -/
  label : Fin d → Frame h q
  /-- Position of a connection label. Values outside the connection set are ignored. -/
  index : Frame h q → Fin d

namespace BaseCycle

variable (c : BaseCycle h q d)

/-- Position of the label for the reverse edge. -/
def reverseIndex (i : Fin d) : Fin d :=
  let s := c.label i
  c.index (-(c.scale (-s.2) * s.1), -s.2)

/-- Rotate at the head after reversing a dart from A (false) or B (true). -/
def nextIndex [NeZero d] (part : Bool) (i : Fin d) : Fin d :=
  if part then c.reverseIndex i + 1 else c.reverseIndex i - 1

/-- A directed edge, specified by its source class, source frame, and local index. -/
abbrev Dart (h q d : Nat) := Bool × Frame h q × Fin d

/-- One application of the facial permutation. -/
def face [NeZero d] (x : Dart h q d) : Dart h q d :=
  (!x.1, compose c.scale x.2.1 (c.label x.2.2), c.nextIndex x.1 x.2.2)

/-- Identity and multiplication laws for the table of powers of the square generator. -/
structure Powers [NeZero h] [NeZero q] (c : BaseCycle h q d) : Prop where
  /-- The exponent zero acts as identity. -/
  zero : c.scale 0 = 1
  /-- Addition of exponents corresponds to multiplication. -/
  add : ∀ k l, c.scale (k + l) = c.scale k * c.scale l

/-- The cycle lists every label in the connection set exactly once. -/
structure Covers [NeZero h] (c : BaseCycle h q d) : Prop where
  /-- Each listed frame gives a disjoint pair. -/
  disjoint : ∀ i, separated c.scale (c.label i) = true
  /-- No local index occurs twice in the inverse lookup. -/
  unique : ∀ i, c.index (c.label i) = i
  /-- Every allowable frame is listed. -/
  complete : ∀ s, separated c.scale s = true → c.label (c.index s) = s

/-- The source frame reached after four steps has zero displacement (Q1),
the index returns (Q2), and the two intermediate opposite corners differ. -/
def checkFace [NeZero h] [NeZero q] [NeZero d] (part : Bool) (i : Fin d) : Bool :=
  let j := c.nextIndex part i
  let k := c.nextIndex (!part) j
  let l := c.nextIndex part k
  let mul := compose c.scale
  let two := mul (c.label i) (c.label j)
  let three := mul two (c.label k)
  mul three (c.label l) == (0, 0) && c.nextIndex (!part) l == i &&
    two != (0, 0) && mul (c.label j) (c.label k) != (0, 0)

private theorem assoc [NeZero h] [NeZero q] (pw : c.Powers) (x y z : Frame h q) :
    compose c.scale (compose c.scale x y) z = compose c.scale x (compose c.scale y z) := by
  apply Prod.ext <;> simp [compose, pw.add] <;> grind

private theorem right_id [NeZero h] [NeZero q] (g : Frame h q) : compose c.scale g (0, 0) = g := by
  apply Prod.ext <;> simp [compose]
  grind

private theorem left_id [NeZero h] [NeZero q] (pw : c.Powers) (g : Frame h q) :
    compose c.scale (0, 0) g = g := by
  simp [compose, pw.zero, Fin.one_mul]

private theorem cancel [NeZero h] [NeZero q] (pw : c.Powers) (g a b : Frame h q)
    (e : compose c.scale g a = compose c.scale g b) : a = b := by
  let inv : Frame h q := (-(c.scale (-g.2) * g.1), -g.2)
  have unit : compose c.scale inv g = (0, 0) := by
    apply Prod.ext <;> simp [compose, inv] <;> grind
  have eq := congrArg (compose c.scale inv) e
  simpa only [← c.assoc pw, unit, c.left_id pw] using eq

/-- The endpoints of the pair labeling a frame, in affine order. -/
def points (g : Frame h q) : Fin h × Fin h := (g.1, g.1 + c.scale g.2)

/-- Increasing representatives of unordered pairs. -/
def sortedPoints (g : Frame h q) : Fin h × Fin h :=
  let (a, b) := c.points g
  if a < b then (a, b) else (b, a)

/-- An explicit bijection between frames and increasing two-subsets. -/
structure Chart (c : BaseCycle h q d) where
  /-- Frame for the two endpoints in increasing order. -/
  decode : Fin h → Fin h → Frame h q
  /-- The two endpoints are distinct. -/
  increasing : ∀ g, (c.sortedPoints g).1 < (c.sortedPoints g).2
  /-- Reading the endpoints recovers the frame. -/
  leftInv : ∀ g, decode (c.sortedPoints g).1 (c.sortedPoints g).2 = g
  /-- Every increasing pair occurs. -/
  rightInv : ∀ a b, a < b → c.sortedPoints (decode a b) = (a, b)

/-- Disjointness of two unordered pairs using any ordered representatives. -/
def Disjoint (p r : Fin h × Fin h) : Prop :=
  p.1 ≠ r.1 ∧ p.1 ≠ r.2 ∧ p.2 ≠ r.1 ∧ p.2 ≠ r.2

/-- Inverse affine frame. -/
def inverse (g : Frame h q) : Frame h q := (-(c.scale (-g.2) * g.1), -g.2)

private theorem scale_unit [NeZero h] [NeZero q] (pw : c.Powers) (k : Fin q) :
    c.scale (-k) * c.scale k = 1 := by
  rw [← pw.add]
  have : -k + k = 0 := by grind
  rw [this, pw.zero]

private theorem mul_inverse [NeZero h] [NeZero q] (pw : c.Powers) (g : Frame h q) :
    compose c.scale g (c.inverse g) = (0, 0) := by
  have := c.scale_unit pw g.2
  apply Prod.ext <;> simp [compose, inverse] <;> grind

private def act (g : Frame h q) (x : Fin h) := g.1 + c.scale g.2 * x

private theorem act_inj [NeZero h] [NeZero q] (pw : c.Powers) (g : Frame h q) {x y : Fin h}
    (he : c.act g x = c.act g y) : x = y := by
  have := c.scale_unit pw g.2
  have eq := congrArg (fun t => c.scale (-g.2) * (t - g.1)) he
  unfold act at eq
  grind

private theorem disjoint_translate [NeZero h] [NeZero q] (pw : c.Powers) (g s : Frame h q) :
    Disjoint (c.points g) (c.points (compose c.scale g s)) ↔ separated c.scale s = true := by
  have coords : c.points (compose c.scale g s) =
      (c.act g s.1, c.act g (s.1 + c.scale s.2)) := by
    apply Prod.ext <;> simp [points, compose, act, pw.add]
    grind
  have origin : c.points g = (c.act g 0, c.act g 1) := by
    apply Prod.ext <;> simp [points, act] <;> grind
  have inj (x y : Fin h) : c.act g x = c.act g y ↔ x = y :=
    ⟨c.act_inj pw g, congrArg _⟩
  rw [coords, origin]
  simp only [Disjoint, separated, Bool.and_eq_true, bne_iff_ne]
  grind

/-- The neighbor list contains exactly the disjoint two-subsets at each vertex. -/
theorem adjacency_iff [NeZero h] [NeZero q] (pw : c.Powers) (covers : c.Covers) (g t : Frame h q) :
    Disjoint (c.points g) (c.points t) ↔ ∃ i, compose c.scale g (c.label i) = t := by
  constructor
  · intro ht
    let s := compose c.scale (c.inverse g) t
    have hgs : compose c.scale g s = t := by
      rw [← c.assoc pw, c.mul_inverse pw, c.left_id pw]
    have hs := (c.disjoint_translate pw g s).mp (hgs ▸ ht)
    exact ⟨c.index s, (congrArg (compose c.scale g) (covers.complete s hs)).trans hgs⟩
  · rintro ⟨i, rfl⟩
    exact (c.disjoint_translate pw g (c.label i)).mpr (covers.disjoint i)

/-- The list has no repeated neighbors. -/
theorem neighbor_injective [NeZero h] [NeZero q] (pw : c.Powers) (covers : c.Covers) (g : Frame h q)
    (i j : Fin d) (e : compose c.scale g (c.label i) = compose c.scale g (c.label j)) : i = j := by
  simpa only [covers.unique] using congrArg c.index (c.cancel pw g _ _ e)

/-- Reverse a dart across its edge. -/
def reverse (x : Dart h q d) : Dart h q d :=
  (!x.1, compose c.scale x.2.1 (c.label x.2.2), c.reverseIndex x.2.2)

/-- Successor around the source vertex, with opposite orders in the two classes. -/
def rotate [NeZero d] (x : Dart h q d) : Dart h q d :=
  (x.1, x.2.1, if x.1 then x.2.2 - 1 else x.2.2 + 1)

/-- The actual facial permutation is rotation after reversal. -/
theorem face_eq [NeZero d] (x : Dart h q d) : c.face x = rotate (c.reverse x) := by
  obtain ⟨p, g, i⟩ := x
  cases p <;> rfl

/-- Left translation followed by an optional exchange of the two parts. -/
def translate (a : Frame h q) (swap : Bool) (x : Dart h q d) : Dart h q d :=
  (swap ^^ x.1, compose c.scale a x.2.1, x.2.2)

/-- Translations preserve dart reversal. -/
theorem translate_reverse [NeZero h] [NeZero q] (pw : c.Powers) (a : Frame h q) (b : Bool)
    (x : Dart h q d) :
    c.translate a b (c.reverse x) = c.reverse (c.translate a b x) := by
  obtain ⟨p, g, i⟩ := x
  cases b <;> cases p <;> simp [translate, reverse, c.assoc pw]

/-- Each signed translation is invertible, with the inverse translation as its inverse. -/
theorem translate_bijective [NeZero h] [NeZero q] (pw : c.Powers) (a : Frame h q) (b : Bool)
    (x : Dart h q d) :
    c.translate (c.inverse a) b (c.translate a b x) = x ∧
    c.translate a b (c.translate (c.inverse a) b x) = x := by
  have unit : compose c.scale (c.inverse a) a = (0, 0) := by
    apply Prod.ext <;> simp [compose, inverse] <;> grind
  obtain ⟨p, g, i⟩ := x
  cases b <;> cases p <;> simp [translate, ← c.assoc pw, unit, c.mul_inverse pw, c.left_id pw]

/-- Keeping the parts preserves orientation, and exchanging them reverses it. -/
theorem translate_rotate [NeZero d] (a : Frame h q) (b : Bool) (x : Dart h q d) :
    (if b then rotate (c.translate a b (rotate x)) else c.translate a b (rotate x)) =
    (if b then c.translate a b x else rotate (c.translate a b x)) := by
  obtain ⟨p, g, i⟩ := x
  cases b <;> cases p <;> simp [rotate, translate] <;> grind

/-- On any two vertices, an invertible dart map sends one to the other,
commutes with reversal, and preserves or reverses all local cyclic orders. -/
def VertexTransitive [NeZero d] : Prop :=
  ∀ (p r : Bool) (g t : Frame h q), ∃ (f inv : Dart h q d → Dart h q d) (flip : Bool),
    (∀ x, inv (f x) = x ∧ f (inv x) = x) ∧
    (∀ x, f (c.reverse x) = c.reverse (f x)) ∧
    (∀ x, (if flip then rotate (f (rotate x)) else f (rotate x)) =
      (if flip then f x else rotate (f x))) ∧
    ∀ i, (f (p, g, i)).1 = r ∧ (f (p, g, i)).2.1 = t

/-- Signed translations act transitively by automorphisms of the rotation system. -/
theorem vertex_transitive [NeZero h] [NeZero q] [NeZero d] (pw : c.Powers) :
    c.VertexTransitive := by
  intro p r g t
  let a := compose c.scale t (c.inverse g)
  let b := r ^^ p
  refine ⟨c.translate a b, c.translate (c.inverse a) b, b, c.translate_bijective pw a b,
    c.translate_reverse pw a b, c.translate_rotate a b, fun i => ?_⟩
  have unit : compose c.scale (c.inverse g) g = (0, 0) := by
    apply Prod.ext <;> simp [compose, inverse] <;> grind
  cases r <;> cases p <;> simp [a, b, translate, c.assoc pw, unit, c.right_id]

/-- The index used for reversal describes the inverse affine frame. -/
theorem label_reverse [NeZero h] [NeZero q] (pw : c.Powers) (covers : c.Covers) (i : Fin d) :
    c.label (c.reverseIndex i) = c.inverse (c.label i) := by
  apply covers.complete
  let s := c.label i
  have hs := (c.disjoint_translate pw (0, 0) s).mpr (covers.disjoint i)
  rw [c.left_id pw] at hs
  apply (c.disjoint_translate pw s (c.inverse s)).mp
  rw [c.mul_inverse pw]
  unfold Disjoint at *
  grind

/-- Dart reversal follows the underlying undirected edge back to its source. -/
theorem reverse_reverse [NeZero h] [NeZero q] (pw : c.Powers) (covers : c.Covers) (x : Dart h q d) :
    c.reverse (c.reverse x) = x := by
  obtain ⟨p, g, i⟩ := x
  have invInv : c.inverse (c.inverse (c.label i)) = c.label i := by
    have hu := c.scale_unit pw (c.label i).2
    apply Prod.ext <;> simp [inverse] <;> grind
  have hi : c.reverseIndex (c.reverseIndex i) = i := by
    change c.index (c.inverse (c.label (c.reverseIndex i))) = i
    rw [c.label_reverse pw covers, invInv, covers.unique]
  simp only [reverse, Bool.not_not, hi, c.label_reverse pw covers, c.assoc pw,
    c.mul_inverse pw, c.right_id]

/-- The finite Q1/Q2 checks imply simple quadrilateral faces at *every* frame.
The second and third conclusions distinguish the two pairs of opposite corners.
Adjacent corners always belong to opposite bipartition classes. -/
theorem quadrilateral [NeZero h] [NeZero q] [NeZero d] (pw : c.Powers)
    (ok : ∀ part i, c.checkFace part i = true) (x : Dart h q d) :
    c.face (c.face (c.face (c.face x))) = x ∧
    (c.face (c.face x)).2.1 ≠ x.2.1 ∧
    (c.face (c.face (c.face x))).2.1 ≠ (c.face x).2.1 := by
  obtain ⟨p, g, i⟩ := x
  have hc := ok p i
  simp only [checkFace, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨prod, label⟩, diag₀⟩, diag₁⟩ := hc
  simp only [face, Bool.not_not, Prod.mk.injEq, true_and]
  constructor
  · refine ⟨?_, label⟩
    simpa only [c.assoc pw, c.right_id] using
      congrArg (compose c.scale g) prod
  · constructor
    · intro he
      apply diag₀
      apply c.cancel pw g
      simpa only [← c.assoc pw, c.right_id] using he
    · intro he
      apply diag₁
      apply c.cancel pw (compose c.scale g (c.label i))
      simpa only [← c.assoc pw, c.right_id] using he

end BaseCycle
end BipartiteKneser
