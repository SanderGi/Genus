import KneserConstruction.FamilyChains
import KneserConstruction.CriterionRows

/-! # The rows attaching the zero-coordinate subgroup -/

noncomputable section

namespace BipartiteKneser.Family.Zero

open Fin.CommRing
open Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Zero-coordinate subgroup element. -/
abbrev Z (m : Multipliers p q) (k : Fin q) := X m k 0

/-- All four labels at a zero-coordinate index with first exponent t. -/
def block (m : Multipliers p q) (t : Fin q) :=
  pair (inverse m) (Z m t) + pair (inverse m) (Z m (t + 1))

theorem inv_Z (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) :
    inverse m (Z m k) = Z m (-k) := by simp only [Z, inverse_X' m h2, neg_zero]

theorem pair_Z_neg (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) :
    pair (inverse m) (Z m (-k)) = pair (inverse m) (Z m k) := by
  simp only [pair, inv_Z m h2, neg_neg]
  ac_rfl

theorem block_reverse (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) :
    block m (-(k + 1)) = block m k := by
  have h : -(k + 1) + 1 = -k := by abel
  simp only [block, h, pair_Z_neg m h2]
  ac_rfl

/-- A row between consecutive zero blocks in the cyclic order. -/
def step (m : Multipliers p q) (k l : Fin q) : Quad (Frame p q) :=
  ⟨Z m k, Z m (k+1), Z m (l+1), Z m l⟩

theorem step_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k l : Fin q) :
    Closed m (step m k l) := by
  simp only [Closed, step, Z, zero_mul m h2]
  congr 1
  abel

/-- The two mixed replacements from Construction 5.6(ii). -/
def bridges (m : Multipliers p q) (a b v : Fin q) : List (Quad (Frame p q)) :=
  [⟨X m (-a) (-1), Z m (-v), X m b (-1), Z m 1⟩,
   ⟨Z m (-(v+1)), X m (-a) 1, X m (-b) (-1), Z m (-2)⟩]

theorem bridges_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0)
    (a b : Fin q) (hs : mult m a + mult m b = -2) (v : Fin q) (hv : v = 1 + a - b) :
    ∀ Q ∈ bridges m a b v, Closed m Q := by
  intro Q h
  simp only [bridges, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · simp only [Closed, attachment_mul m h2 a b hs, Z, zero_mul m h2]
    congr 1
    rw [hv]
    ring
  · let x : Criterion.AffineFrame m := X m a (-1)
    let y : Criterion.AffineFrame m := X m (-b) (-1)
    let z : Criterion.AffineFrame m := Z m (-(v+1))
    let t : Criterion.AffineFrame m := Z m (-2)
    let u : Criterion.AffineFrame m := X m (-a) 1
    have invx : x⁻¹ = u := by
      change inverse m (X m a (-1)) = _
      rw [inverse_X' m h2, neg_neg]
    change z * y = t * u
    rw [← invx, eq_mul_inv_iff_mul_eq, mul_assoc]
    change compose m.power (Z m (-(v+1))) (compose m.power (X m (-b) (-1)) (X m a (-1))) = _
    rw [attachment_mul m h2 b a (by rwa [add_comm])]
    change compose m.power (X m _ 0) (X m _ 0) = X m _ 0
    rw [zero_mul m h2]
    congr 1
    rw [hv]
    ring

theorem bridges_domains (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (a b v : Fin q) :
    ((bridges m a b v).map (Quad.domBag (inverse m))).sum = quartet m a 1 + block m v := by
  simp only [bridges, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Quad.domBag, block, quartet, pair, Z, inverse_X' m h2, neg_neg, neg_zero]
  ac_rfl

theorem bridges_ranges (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (a b v : Fin q) :
    ((bridges m a b v).map (Quad.ranBag (inverse m))).sum = quartet m b 1 + block m 1 := by
  simp only [bridges, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Quad.ranBag, block, quartet, pair, Z, inverse_X' m h2, neg_neg, neg_zero,
    show (1 : Fin q) + 1 = 2 from (Nat.cast_add (R := Fin q) 1 1).symm]
  ac_rfl

/-- Parity-dependent local replacements from Construction 5.6(iii). -/
def templates (m : Multipliers p q) (odd : Bool) : List (Quad (Frame p q)) :=
  if odd then
    [⟨Z m 1, Z m (-2), Z m 3, Z m 6⟩, ⟨Z m 3, Z m 4, Z m (-4), Z m (-5)⟩,
     ⟨Z m 5, Z m 6, Z m (-7), Z m (-8)⟩]
  else [⟨Z m 1, Z m 3, Z m (-3), Z m (-5)⟩, ⟨Z m 2, Z m 4, Z m (-4), Z m (-6)⟩]

theorem templates_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (odd : Bool) :
    ∀ Q ∈ templates m odd, Closed m Q := by
  intro Q h
  cases odd <;> simp only [templates, ite_true, Bool.false_eq_true, ite_false, List.mem_cons,
    List.not_mem_nil, or_false] at h
  · rcases h with rfl | rfl <;> simp only [Closed, Z, zero_mul m h2] <;> congr 1 <;>
      ring
  · rcases h with rfl | rfl | rfl <;> simp only [Closed, Z, zero_mul m h2] <;> congr 1 <;>
      ring

/-- Blocks at indices strictly before the end of the replacement. -/
def initial (m : Multipliers p q) (odd : Bool) :=
  block m 1 + block m 3 + (if odd then block m 5 else 0)

/-- Blocks at successors of those indices. -/
def following (m : Multipliers p q) (odd : Bool) :=
  block m 3 + block m 5 + (if odd then block m 7 else 0)

theorem templates_inventories (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (odd : Bool) :
    ((templates m odd).map (Quad.domBag (inverse m))).sum = initial m odd ∧
    ((templates m odd).map (Quad.ranBag (inverse m))).sum = following m odd := by
  cases odd <;> constructor
  all_goals
    simp only [templates, initial, following, Bool.false_eq_true, ite_false, ite_true,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Quad.domBag, Quad.ranBag,
      block, pair_Z_neg m h2]
    simp only [show (1 : Fin q) + 1 = 2 from (Nat.cast_add (R := Fin q) 1 1).symm,
      show (3 : Fin q) + 1 = 4 from (Nat.cast_add (R := Fin q) 3 1).symm,
      show (5 : Fin q) + 1 = 6 from (Nat.cast_add (R := Fin q) 5 1).symm,
      show (7 : Fin q) + 1 = 8 from (Nat.cast_add (R := Fin q) 7 1).symm]
    ac_rfl

end BipartiteKneser.Family.Zero
