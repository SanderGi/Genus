import BipartiteKneser.Certificates
import BipartiteKneser.Graph
import BipartiteKneser.Faces
import BipartiteKneser.Euler

/-!
# Minimum orientable genus in the rotation-system model

An arbitrary cyclic neighbor order at a vertex is a numbering of its incident
darts modulo the degree. The face permutation reverses a dart across its edge
and takes the successor in the numbering at its head. Euler's formula assigns
a genus to the resulting orientable cellular embedding of the connected graph.
-/

namespace BipartiteKneser

private def productList (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map (Prod.mk x)

private theorem product_length (xs : List α) (ys : List β) :
    (productList xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [productList]
  | cons x xs ih =>
    simp only [productList, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

private theorem product_nodup {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup) :
    (productList xs ys).Nodup := by
  induction xs with
  | nil => simp [productList]
  | cons x xs ih =>
    rw [List.nodup_cons] at hx
    rw [productList, List.flatMap_cons, List.nodup_append]
    refine ⟨hy.map (Prod.mk x) (by grind), ih hx.2, ?_⟩
    simp
    grind

private def darts (h q d : Nat) : List (BaseCycle.Dart h q d) :=
  productList [false, true]
    (productList (productList (List.finRange h) (List.finRange q)) (List.finRange d))

private theorem dart_count (h q d : Nat) : (darts h q d).length = 2 * (h*q*d) := by
  simp [darts, product_length]

private theorem dart_nodup (h q d : Nat) : (darts h q d).Nodup :=
  product_nodup (by decide) (product_nodup
    (product_nodup (List.nodup_finRange h) (List.nodup_finRange q)) (List.nodup_finRange d))

private theorem mem_darts (x : BaseCycle.Dart h q d) : x ∈ darts h q d := by
  obtain ⟨p, ⟨a,b⟩, i⟩ := x
  cases p <;> simp [darts, productList, List.mem_finRange]

/-- A bijection from cyclic positions to neighbor labels, with explicit inverse. -/
structure LocalOrder (d : Nat) where
  /-- Label at a position. -/
  label : Fin d → Fin d
  /-- Position of a label. -/
  position : Fin d → Fin d
  /-- Labels determine positions uniquely. -/
  leftInv : ∀ j, position (label j) = j
  /-- Every label occurs. -/
  rightInv : ∀ i, label (position i) = i

namespace BaseCycle

variable {h q d : Nat} (c : BaseCycle h q d)

/-- An independent cyclic neighbor order at each vertex. -/
abbrev Orders (h q d : Nat) := Bool → Frame h q → LocalOrder d

/-- Facial traversal for any rotation system on this graph. -/
def walkFace [NeZero d] (o : Orders h q d) (x : Dart h q d) : Dart h q d :=
  let (p, g, i) := c.reverse x
  let r := o p g
  (p, g, r.label (r.position i + 1))

private theorem no_fixed [NeZero d] (hd : 1 < d) (r : LocalOrder d) (i : Fin d) :
    r.label (r.position i + 1) ≠ i := by
  intro eq
  have he := congrArg r.position eq
  rw [r.leftInv] at he
  have hn : (1 : Fin d) ≠ 0 := by
    intro hc
    have hv := congrArg Fin.val hc
    simp at hv
    omega
  grind

private theorem walk_girth [NeZero h] [NeZero q] [NeZero d] (hd : 1 < d)
    (pw : c.Powers) (cv : c.Covers) (o : Orders h q d) : GirthFour (c.walkFace o) := by
  rintro ⟨p, g, i⟩
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have := congrArg Prod.fst he
    cases p <;> contradiction
  · intro he
    let x : Dart h q d := (p, g, i)
    let v := c.reverse x
    let r := o v.1 v.2.1
    have back := congrArg (fun z : Dart h q d => z.2.1) (c.reverse_reverse pw cv x)
    have target := congrArg (fun z : Dart h q d => z.2.1) he
    apply no_fixed hd r v.2.2
    apply c.neighbor_injective pw cv v.2.1
    exact target.trans back.symm
  · intro he
    have := congrArg Prod.fst he
    cases p <;> contradiction

private def standardOrders [NeZero d] : Orders h q d := fun p _ =>
  if p then ⟨Neg.neg, Neg.neg, by intro i; grind, by intro i; grind⟩
  else ⟨id, id, by simp, by simp⟩

private theorem standard_face [NeZero d] (x : Dart h q d) :
    c.walkFace standardOrders x = c.face x := by
  obtain ⟨p, g, i⟩ := x
  cases p <;> simp [walkFace, standardOrders, face, nextIndex, reverse]
  grind

/-- These cyclic orders give an orientable cellular embedding with Euler characteristic 2 − 2g. -/
def HasGenus [NeZero d] (o : Orders h q d) (g : Int) : Prop :=
  ∃ fs : List (List (Dart h q d)),
    FacePartition (c.walkFace o) (darts h q d) fs ∧
    2 - 2*g = 2*(h : Int)*q - (h : Int)*q*d + fs.length

/-- The affine rotation attains g, and every cyclic ordering has genus at least g. -/
def MinimumGenus [NeZero d] (g : Int) : Prop :=
  c.HasGenus standardOrders g ∧ ∀ o k, c.HasGenus o k → g ≤ k

/-- For a connected graph in affine coordinates, the quadrangulation attains
the Euler lower bound among all cyclic orders at all vertices. -/
theorem minimum_of_four [NeZero h] [NeZero q] [NeZero d] (hd : 1 < d)
    (pw : c.Powers) (cv : c.Covers) (closed : ∀ x, c.face (c.face (c.face (c.face x))) = x)
    (g : Int) (formula : 4*(g + (h : Int)*q - 1) = (h : Int)*q*d) : c.MinimumGenus g := by
  have faceEq : c.walkFace standardOrders = c.face := funext c.standard_face
  have cf : ∀ x, c.walkFace standardOrders (c.walkFace standardOrders
      (c.walkFace standardOrders (c.walkFace standardOrders x))) = x := faceEq ▸ closed
  obtain ⟨fs, legal, count⟩ := four_partition _ (c.walk_girth hd pw cv standardOrders) cf
    (darts h q d) (dart_nodup ..) (fun _ _ => mem_darts _)
  have dc := dart_count h q d
  have icount : (4 : Int) * fs.length = 2*((h : Int)*q*d) := by
    exact_mod_cast count.trans dc
  constructor
  · refine ⟨fs, legal, ?_⟩
    grind
  · rintro o k ⟨faces, partition, euler⟩
    have hb := face_bound (c.walk_girth hd pw cv o) partition
    rw [dc] at hb
    have hi : (4 : Int)*faces.length ≤ 2*((h : Int)*q*d) := by exact_mod_cast hb
    grind

end BaseCycle

/-- Theorem 1.1 in the combinatorial rotation-system model. The same affine
cycle witnesses both vertex transitivity and attainment of the minimum genus. -/
def OptimalRotation (h : Nat) : Prop :=
  let q := (h - 1) / 2
  let d := (h - 2) * (h - 3) / 2
  ∃ (hh : NeZero h) (hq : NeZero q) (hd : NeZero d),
    letI := hh
    letI := hq
    letI := hd
    ∃ c : BaseCycle h q d, Nonempty c.Chart ∧ c.Powers ∧ c.Covers ∧
      (∀ x, c.face (c.face (c.face (c.face x))) = x ∧
        (c.face (c.face x)).2.1 ≠ x.2.1 ∧
        (c.face (c.face (c.face x))).2.1 ≠ (c.face x).2.1) ∧
      c.VertexTransitive ∧
      c.MinimumGenus (genusFormula h)

private theorem optimal {h : Nat} [NeZero h] [NeZero ((h - 1) / 2)]
    [NeZero ((h - 2) * (h - 3) / 2)]
    (qr : HasAffineQuadrangulation h ((h - 1) / 2) ((h - 2) * (h - 3) / 2))
    (degree : 1 < (h - 2) * (h - 3) / 2)
    (formula : 4 * (genusFormula h + (h : Int) * (((h - 1) / 2 : Nat) : Int) - 1) =
      (h : Int) * (((h - 1) / 2 : Nat) : Int) * (((h - 2) * (h - 3) / 2 : Nat) : Int)) :
    OptimalRotation h := by
  obtain ⟨c, ch, pw, cv, _, faces, trans⟩ := qr
  exact ⟨inferInstance, inferInstance, inferInstance, c, ch, pw, cv, faces, trans,
    c.minimum_of_four degree pw cv (fun x => (faces x).1) _ formula⟩

/-- For every admissible order, constructing the affine quadrangulation
suffices to obtain both conclusions of Theorem 1.1. -/
theorem optimal_of_quadrangulation {h : Nat} [NeZero h] [NeZero ((h - 1) / 2)]
    [NeZero ((h - 2) * (h - 3) / 2)] (large : 3 < h) (residue : h % 8 = 3)
    (qr : HasAffineQuadrangulation h ((h - 1) / 2) ((h - 2) * (h - 3) / 2)) :
    OptimalRotation h := by
  let t := h / 8
  have ht : h = 8*t + 3 := by dsimp [t]; omega
  have htpos : 0 < t := by omega
  have qval : (h - 1) / 2 = 4*t + 1 := by omega
  have h₂ : (h - 2) * (h - 3) = 8 * (t*(8*t+1)) := by
    have ha : h - 2 = 8*t+1 := by omega
    have hb : h - 3 = 8*t := by omega
    rw [ha, hb]
    grind
  have dval : (h - 2) * (h - 3) / 2 = 4 * (t*(8*t+1)) := by omega
  apply optimal qr
  · rw [dval]
    have : 0 < t*(8*t+1) := Nat.mul_pos htpos (by omega)
    omega
  · have hI : (h : Int) = 8*(t : Int) + 3 := by exact_mod_cast ht
    have hp : (h : Int)*(h-1) = 2*((h : Int)*(4*(t : Int)+1)) := by rw [hI]; grind
    have he : (h : Int)*(h-1)*(h-2)*(h-3) =
        16*((h : Int)*(4*(t : Int)+1)*((t : Int)*(8*t+1))) := by rw [hI]; grind
    unfold genusFormula
    rw [he, hp, dval, qval]
    simp only [Int.mul_ediv_cancel_left _ (by decide : (16 : Int) ≠ 0),
      Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0), Int.natCast_add, Int.natCast_mul]
    grind

end BipartiteKneser
