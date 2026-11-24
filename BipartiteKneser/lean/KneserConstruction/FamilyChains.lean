import KneserConstruction.FamilyLedger
import KneserConstruction.Coordinates

/-!
# Successor rows inside coordinate fibers

A path consists of its first oriented exponent followed by the remaining
oriented exponents. The target of each transition may be sign-switched.
The two inventory identities leave precisely the last domain and first range
blocks unused, including for a path consisting of a single exponent.
-/

noncomputable section

namespace BipartiteKneser.Family

open Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- A row satisfies the affine closure equation of Definition 3.4. -/
def Closed (m : Multipliers p q) (Q : Quad (Frame p q)) : Prop :=
  compose m.power Q.a Q.c = compose m.power Q.d Q.b

/-- The four labels belonging to one exponent pair and one coordinate fiber. -/
def quartet (m : Multipliers p q) (k : Fin q) (w : ZMod p) :=
  pair (inverse m) (X m k w) + pair (inverse m) (X m k (-w))

theorem inverse_X' (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ZMod p) :
    inverse m (X m k w) = X m (-k) (-w) := inverse_X m h2 k w

theorem quartet_neg (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ZMod p) :
    quartet m (-k) w = quartet m k w := by
  simp only [quartet, pair, inverse_X' m h2, neg_neg]
  ac_rfl

/-- The canonical transition, including the switched target orientation. -/
def canonical (m : Multipliers p q) (k l : Fin q) (w : ZMod p) (switch : Bool) :
    Quad (Frame p q) :=
  let t := if switch then -l else l
  ⟨X m k w, X m k (-w), X m t (-w), X m t w⟩

theorem canonical_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0)
    (k l : Fin q) (w : ZMod p) (s : Bool) : Closed m (canonical m k l w s) :=
  canonical_row m h2 k _ w

theorem canonical_dom (m : Multipliers p q) (k l : Fin q) (w : ZMod p) (s : Bool) :
    (canonical m k l w s).domBag (inverse m) = quartet m k w := rfl

theorem canonical_ran (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0)
    (k l : Fin q) (w : ZMod p) (s : Bool) :
    (canonical m k l w s).ranBag (inverse m) = quartet m l w := by
  cases s
  · exact add_comm ..
  · exact (add_comm ..).trans (quartet_neg m h2 l w)

/-- Canonical successor rows for the path `k :: tail`. -/
def chain (m : Multipliers p q) (w : ZMod p) (switch : Fin q → Bool) (k : Fin q) :
    List (Fin q) → List (Quad (Frame p q))
  | [] => []
  | l :: ls => canonical m k l w (switch k) :: chain m w switch l ls

theorem chain_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p)
    (s : Fin q → Bool) (k : Fin q) (ls : List (Fin q)) :
    ∀ Q ∈ chain m w s k ls, Closed m Q := by
  induction ls generalizing k with
  | nil => simp [chain]
  | cons l ls ih =>
    intro Q h
    rcases List.mem_cons.mp h with rfl | h
    · exact canonical_closed m h2 ..
    · exact ih l Q h

/-- Proposition 4.9, counting every label in the path with multiplicity. -/
theorem chain_inventory (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p)
    (s : Fin q → Bool) (k : Fin q) (ls : List (Fin q)) :
    let rows := chain m w s k ls
    let total := ((k :: ls).map (quartet m · w)).sum
    (rows.map (Quad.domBag (inverse m))).sum + quartet m (ls.getLastD k) w = total ∧
      (rows.map (Quad.ranBag (inverse m))).sum + quartet m k w = total := by
  induction ls generalizing k with
  | nil => simp [chain]
  | cons l ls ih =>
    obtain ⟨hd, hr⟩ := ih l
    simp only [chain, List.map_cons, List.sum_cons, canonical_dom, canonical_ran m h2,
      List.getLastD_cons] at *
    constructor
    · rw [add_assoc, hd]
    · calc
        _ = quartet m k w +
            ((List.map (Quad.ranBag (inverse m)) (chain m w s l ls)).sum + quartet m l w) := by
              ac_rfl
        _ = _ := congrArg (quartet m k w + ·) hr

end BipartiteKneser.Family
