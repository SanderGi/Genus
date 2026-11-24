import KneserConstruction.BoundaryPermutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Symbolic normalization of the boundary labels (Proposition 7.2, Appendix A.6) -/

namespace BipartiteKneser.Boundary

/-- A positive fiber number and the two flags for negative exponent and negative coordinate. -/
abbrev Point := Int × Bool × Bool

/-- Number of outside fibers below the ordinary interval. -/
def leftCount : Case → Nat
  | .one => 3
  | .two => 4

/-- Recover the coordinate of the outside fiber at index `i`. -/
def outside (c : Case) (q : Int) (i : Nat) : Int :=
  if i < leftCount c then (i : Int) + 1 else q - (count c - i : Nat)

/-- Coordinates of the six ordered strand endpoints based at a given fiber. -/
def port (base : Int) (j : Nat) : Point :=
  (if j = 2 ∨ j = 5 then base + 1 else base, decide (1 ≤ j ∧ j ≤ 3), decide (3 ≤ j))

/-- Interpret a numbered boundary label as a fiber and a pair of signs. -/
def decode (c : Case) (q : Int) (x : Label c) : Point :=
  if x.val < 4 * count c then
    (outside c q (x.val / 4), x.val.testBit 1, x.val.testBit 0)
  else port (leftCount c + 1 : Nat) (x.val - 4 * count c)

/-- The ordinary and exceptional values of `z_w` in Construction 4.11. -/
def zValue (c : Case) (q w : Int) : Int := match c with
  | .one =>
    if w = 1 then q - 1 else if w = 3 then q + 3 else if w = q - 9 then -3
    else if w = q - 4 then 2 else if w = q - 2 then -5 else w + 1
  | .two =>
    if w = 1 then -2 else if w = 4 then 1 else if w = q - 10 then q - 4
    else if w = q - 5 then -1 else if w = q - 4 then -3 else if w = q - 3 then -6
    else if w = q - 2 then -(q - 3) else w + 1

/-- Shift a boundary output by one modulus when it lies outside the centered range. -/
def center (q v : Int) : Int :=
  if q < v then v - (2 * q + 1) else if v < -q then v + (2 * q + 1) else v

/-- Centering preserves the residue modulo `2 * q + 1`. -/
theorem center_mod (q v : Int) : center q v % (2 * q + 1) = v % (2 * q + 1) := by
  unfold center
  split_ifs <;> simp

/-- Proposition 6.5 on the last exponent pair, including the translation splice. -/
def routePoint (c : Case) (q w : Int) (slot : Nat) : Point :=
  let e := slot.testBit 1
  let t := slot.testBit 0
  if w = q - 1 then (if c = .one then 1 else q - 2, e, !t)
  else
    let z := zValue c q w
    let v := if e then -(w - 2 * z) else z
    let k := center q (if t then -v else v)
    (if k < 0 then -k else k, e ^^ t, decide (k < 0))

/-- The coordinate rule before relabeling, using the missing-fiber bit and the switch bit.
At an entry both bits are ignored. -/
def coordinateStep (c : Case) (q : Int) (missing switch : Bool) (p r : Interval.Perm)
    (x : Label c) : Point :=
  if x.val < 4 * count c then
    routePoint c q (outside c q (x.val / 4)) (lastSlot (x.val / 4) (x.val % 4) missing switch)
  else
    port (q - (count c - leftCount c : Nat)) (transferIndex p r (x.val - 4 * count c))

set_option maxHeartbeats 12000000 in
-- Discharge the 26 fibers times four slots with symbolic integer arithmetic.
private theorem decode_route (c : Case) (q : Int) (hq : 65 ≤ q)
    (i : Fin (count c)) (j : Fin 4) :
    decode c q (Fin.ofNat _ (routeIndex c i.val j.val)) =
      routePoint c q (outside c q i.val) j.val := by
  cases c <;> fin_cases i <;> fin_cases j <;>
    simp +ground (disch := omega) [decode, outside, port, count, leftCount, routePoint,
      zValue, center, ite_eq_left, ite_eq_right, decide_eq_true] <;> omega

private theorem decode_exit (c : Case) (q : Int) (j : Fin 6) :
    decode c q (Fin.ofNat _ (exitIndex c j.val)) =
      port (q - (count c - leftCount c : Nat)) j.val := by
  cases c <;> fin_cases j <;>
    simp +ground [exitIndex, decode, port, outside, leftCount, count] <;> omega

/-- Appendix A.6. Decoding commutes with every outside assignment and every entry
transfer uniformly in q. The representative q=41 used by the encoder disappears. -/
theorem normalize_step (c : Case) (q : Int) (hq : 65 ≤ q)
    (chars : Pattern c) (mask : Nat) (p r : Interval.Perm) (x : Label c) :
    decode c q (step c chars mask p r x) =
      coordinateStep c q (chars.val.testBit (x.val / 4)) (mask.testBit (x.val / 4)) p r x := by
  unfold step nextIndex coordinateStep
  split <;> rename_i h
  · exact decode_route c q hq ⟨x.val / 4, by omega⟩ ⟨_, lastSlot_lt ..⟩
  · exact decode_exit c q ⟨_, transferIndex_lt ..⟩

end BipartiteKneser.Boundary
