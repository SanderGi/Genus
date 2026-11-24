module

public import Std

/-!
# Joining the K and N fibers

The two columns of Construction 4.11 are expressed in the signed
representatives from −q to q of residues modulo 2q+1. The inverse map
identifies the unique source and column for each required N coordinate.
-/

@[expose] public section

set_option linter.all true

namespace BipartiteKneser.FiberJoins

/-- The two choices of N, distinguished by the residue of the prime modulo three. -/
inductive Case where
  /-- The multiplier of N is −1/3. -/
  | one
  /-- The multiplier of N is −2/3. -/
  | two

/-- The admissible range for the coordinate table in Construction 4.11. -/
def InRange : Case → Int → Prop
  | .one, q => 21 ≤ q
  | .two, q => 29 ≤ q

/-- The fiber missing the N-exponent pair. -/
def missing : Case → Int → Int
  | .one, _ => 1
  | .two, q => q - 2

/-- Signed coordinate outputs (y,z). Each exceptional row is reduced
modulo 2q+1 to its signed representative. -/
def row : Case → Int → Int → Int × Int
  | .one, q, w =>
    if w = 1 then (4, q - 1)
    else if w = 3 then (-2, 2 - q)
    else if w = q - 9 then (q - 3, -3)
    else if w = q - 4 then (q - 8, 2)
    else if w = q - 2 then (7 - q, -5)
    else (-w - 2, w + 1)
  | .two, q, w =>
    if w = 1 then (5, -2)
    else if w = 4 then (2, 1)
    else if w = q - 10 then (q - 1, q - 4)
    else if w = q - 5 then (q - 3, -1)
    else if w = q - 4 then (1 - q, -3)
    else if w = q - 3 then (8 - q, -6)
    else if w = q - 2 then (q - 9, 3 - q)
    else (-w - 2, w + 1)

/-- Signed target of an inverse pair in a K-to-N quadruple; false selects y. -/
def target (c : Case) (q w : Int) (col : Bool) : Int :=
  if col then (row c q w).2 else (row c q w).1

/-- Inverse lookup. Ordinary positive outputs come from z=w+1 and ordinary
negative outputs from y=−w−2. -/
def source : Case → Int → Int → Int × Bool
  | .one, q, t =>
    if t = 4 then (1, false) else if t = q-1 then (1, true)
    else if t = -2 then (3, false) else if t = 2-q then (3, true)
    else if t = q-3 then (q-9, false) else if t = -3 then (q-9, true)
    else if t = q-8 then (q-4, false) else if t = 2 then (q-4, true)
    else if t = 7-q then (q-2, false) else if t = -5 then (q-2, true)
    else if 0 < t then (t-1, true) else (-t-2, false)
  | .two, q, t =>
    if t = 5 then (1, false) else if t = -2 then (1, true)
    else if t = 2 then (4, false) else if t = 1 then (4, true)
    else if t = q-1 then (q-10, false) else if t = q-4 then (q-10, true)
    else if t = q-3 then (q-5, false) else if t = -1 then (q-5, true)
    else if t = 1-q then (q-4, false) else if t = -3 then (q-4, true)
    else if t = 8-q then (q-3, false) else if t = -6 then (q-3, true)
    else if t = q-9 then (q-2, false) else if t = 3-q then (q-2, true)
    else if 0 < t then (t-1, true) else (-t-2, false)

/-- Exactly the signed indices needed in the N ranges of Proposition 4.12. -/
def Required (c : Case) (q t : Int) : Prop :=
  -q < t ∧ t < q ∧ t ≠ 0 ∧ t ≠ missing c q ∧ t ≠ -(missing c q)

/-- Each row satisfies y+2z=w in the field of residues modulo 2q+1. -/
theorem closure (c : Case) (q w : Int) :
    (row c q w).1 + 2 * (row c q w).2 = w ∨
    (row c q w).1 + 2 * (row c q w).2 = w + (2*q+1) ∨
    (row c q w).1 + 2 * (row c q w).2 = w - (2*q+1) := by
  cases c <;> unfold row <;> repeat' split
  all_goals (dsimp; omega)

set_option maxHeartbeats 4000000 in
/-- Every output is required, and its source and column are unique. -/
theorem source_target (c : Case) {q w : Int} (hq : InRange c q)
    (lo : 1 ≤ w) (hi : w ≤ q-2) (col : Bool) :
    Required c q (target c q w col) ∧ source c q (target c q w col) = (w, col) := by
  cases c <;> cases col <;> simp only [target, Bool.false_eq_true, ite_false, ite_true, row,
    Required, missing, InRange] at *
  all_goals repeat' split
  all_goals dsimp only
  all_goals unfold source
  all_goals grind (splits := 32)

set_option maxHeartbeats 4000000 in
/-- Every required N coordinate occurs as an output. -/
theorem target_source (c : Case) {q t : Int} (hq : InRange c q) (ht : Required c q t) :
    1 ≤ (source c q t).1 ∧ (source c q t).1 ≤ q-2 ∧
    target c q (source c q t).1 (source c q t).2 = t := by
  cases c <;> simp only [source, Required, missing, InRange] at *
  all_goals repeat' split
  all_goals try dsimp only
  all_goals simp only [target, Bool.false_eq_true, ite_false, ite_true, row]
  all_goals grind (splits := 32)

end BipartiteKneser.FiberJoins
