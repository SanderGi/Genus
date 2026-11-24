module

public import KneserConstruction.FamilyChains
public import KneserConstruction.FamilyJoins

/-! # Fiber rows after removing the transition at the attachment -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Family

open Coordinates FiberJoins

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Exactly the final canonical transition can be switched. -/
def toLast (m : Multipliers p q) (w : ZMod p) (s : Bool) (head : Fin q)
    (middle : List (Fin q)) (last : Fin q) :=
  chain m w (fun _ => false) head middle ++
    [canonical m (middle.getLastD head) last w s]

/-- The coordinate and the distinguished endpoints use a zero-based positive-fiber index. -/
def coord (i : Fin (q - 1)) : ZMod p := ((i.val + 1 : ℕ) : ZMod p)

/-- Use E at the fiber missing N and N at every other first block. -/
def firstExp (c : Case) (N E : Fin q) (i : Fin (q - 1)) :=
  if (i.val : ℤ) + 1 = missing c q then E else N

/-- Use E at the fiber q−1 and K at every other final block. -/
def lastExp (K E : Fin q) (i : Fin (q - 1)) :=
  if i.val + 1 = q - 1 then E else K

/-- All oriented exponent representatives in the chosen order at a fiber. -/
def fiberOrder (f l a b : Fin q) (middle : List (Fin q)) (attach : Bool) :=
  (if attach then [f,a,b] else [f]) ++ middle ++ [l]

/-- At the special fiber the a-to-b row has been transferred to the zero-coordinate block. -/
def fiberRows (m : Multipliers p q) (w : ZMod p) (s : Bool) (f l a b : Fin q)
    (middle : List (Fin q)) (attach : Bool) :=
  if attach then canonical m f a w false :: toLast m w s b middle l
  else toLast m w s f middle l

theorem toLast_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p) (s : Bool)
    (f l : Fin q) (middle : List (Fin q)) : ∀ Q ∈ toLast m w s f middle l, Closed m Q := by
  intro Q h
  rcases List.mem_append.mp h with h | h
  · exact chain_closed m h2 w _ f middle Q h
  · obtain rfl := List.mem_singleton.mp h
    exact canonical_closed m h2 ..

theorem fiberRows_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p) (s : Bool)
    (f l a b : Fin q) (middle : List (Fin q)) (attach : Bool) :
    ∀ Q ∈ fiberRows m w s f l a b middle attach, Closed m Q := by
  cases attach
  · exact toLast_closed m h2 w s f l middle
  · intro Q h
    rcases List.mem_cons.mp h with rfl | h
    · exact canonical_closed m h2 ..
    · exact toLast_closed m h2 w s b l middle Q h

private theorem toLast_counts (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0)
    (w : ZMod p) (s : Bool) (f l : Fin q) (middle : List (Fin q)) :
    let rows := toLast m w s f middle l
    (rows.map (Quad.domBag (inverse m))).sum = ((f :: middle).map (quartet m · w)).sum ∧
    (rows.map (Quad.ranBag (inverse m))).sum + quartet m f w =
      ((f :: middle).map (quartet m · w)).sum + quartet m l w := by
  obtain ⟨hd,hr⟩ := chain_inventory m h2 w (fun _ => false) f middle
  simp only [toLast, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, canonical_dom, canonical_ran m h2] at *
  exact ⟨hd, by rw [add_right_comm, hr]⟩

/-- Exactly the end blocks and (at 1) the excised a-to-b transition are outstanding. -/
theorem fiberRows_counts (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p)
    (s : Bool) (f l a b : Fin q) (middle : List (Fin q)) (attach : Bool) :
    let rows := fiberRows m w s f l a b middle attach
    let all := ((fiberOrder f l a b middle attach).map (quartet m · w)).sum
    (rows.map (Quad.domBag (inverse m))).sum + quartet m l w +
      (if attach then quartet m a w else 0) = all ∧
    (rows.map (Quad.ranBag (inverse m))).sum + quartet m f w +
      (if attach then quartet m b w else 0) = all := by
  cases attach
  · obtain ⟨hd,hr⟩ := toLast_counts m h2 w s f l middle
    simp only [fiberRows, fiberOrder, Bool.false_eq_true, ite_false, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at *
    exact ⟨by rw [hd], by rw [hr]⟩
  · obtain ⟨hd,hr⟩ := toLast_counts m h2 w s b l middle
    simp only [fiberRows, fiberOrder, ite_true, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, canonical_dom,
      canonical_ran m h2] at *
    constructor
    · rw [hd]
      ac_rfl
    · calc
        _ = quartet m f w + quartet m a w +
          (((toLast m w s b middle l).map (Quad.ranBag (inverse m))).sum + quartet m b w) := by
            ac_rfl
        _ = _ := by rw [hr]; ac_rfl

end BipartiteKneser.Family
