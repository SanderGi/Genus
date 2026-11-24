import KneserConstruction.FamilyEnds
import KneserConstruction.FamilyZero
import KneserConstruction.FamilyTranslations
import KneserConstruction.CoordinateSpecial
import KneserConstruction.Parameters

/-! # Row indices and quadruples for the complete generic construction -/

noncomputable section

namespace BipartiteKneser.Family

open Fin.CommRing
open Coordinates FiberJoins

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Choices for the generic construction, including the freely ordered interior at each fiber. -/
structure Construction (m : Multipliers p q) where
  /-- Number of four-label blocks in the zero-coordinate fiber. -/
  M : ℕ
  large : 16 ≤ M
  p_eq : p = 8 * M + 3
  q_eq : q = 4 * M + 1
  /-- The three distinguished exponents K, N, and E. -/
  special : Special m
  /-- The two exponents and zero-block index from Lemma 5.5. -/
  params : Parameters.Exponents m special.K special.N special.E
  /-- Interior exponents after removing the prescribed prefix and final exponent. -/
  middle : Fin (q - 1) → List (Fin q)

namespace Construction

variable {m : Multipliers p q} (C : Construction m)

/-- Residue case in the joining table. -/
def residueCase (p : ℕ) : Case := if p % 3 = 1 then .one else .two

/-- First oriented exponent at this positive fiber. -/
abbrev first (i : Fin (q - 1)) := firstExp (residueCase p) C.special.N C.special.E i
/-- Final oriented exponent at this positive fiber. -/
abbrev last (i : Fin (q - 1)) := lastExp C.special.K C.special.E i

/-- Full order including the two ends and the terms reserved for the attachment. -/
def order (i : Fin (q - 1)) :=
  fiberOrder (C.first i) (C.last i) C.params.a C.params.b (C.middle i) (decide (i.val = 0))

/-- Ordinary rows with the one transition removed at the fiber represented by 1. -/
def ordinary (switch : ℕ → Bool) (i : Fin (q - 1)) :=
  fiberRows m (coord i) (switch (i.val + 1)) (C.first i) (C.last i) C.params.a C.params.b
    (C.middle i) (decide (i.val = 0))

/-- K-to-N transition rows indexed by positive coordinates below q−1. -/
abbrev joins := Joins.row m C.special.K C.special.N (residueCase p)
/-- Translation rows after the replacements at the two cut indices. -/
abbrev translations := Translations.row m (Translations.paperLayout p C.M C.large) C.special.E
  ((q - 1 : ℕ) : ZMod p) (Translations.w₀ p q)
/-- Oriented exponent of the zero pair attached at fiber one. -/
abbrev v := 1 + C.params.a - C.params.b
/-- Zero-coordinate rows, including the two mixed attachment rows. -/
abbrev zeros := Zero.rows m C.M C.params.j C.params.a C.params.b C.v

/-- The chosen orders enumerate the connection set together with the translation and zero blocks. -/
def CoversOrders : Prop :=
  inventory m = Translations.translationBag m (2 * C.M) +
    (∑ i : Fin C.M, Zero.block m (Zero.start i.val)) +
    ∑ i, ((C.order i).map (quartet m · (coord i))).sum

/-- The four disjoint row address spaces. -/
abbrev Row (switch : ℕ → Bool) :=
  (Σ i, Fin (C.ordinary switch i).length) ⊕
    (Fin (q - 2) ⊕ (Translations.Row (2 * C.M) ⊕ Fin C.zeros.length))

/-- The actual quadruple at a row address. -/
def row (switch : ℕ → Bool) : C.Row switch → Quad (Frame p q)
  | .inl ⟨i,j⟩ => (C.ordinary switch i).get j
  | .inr (.inl j) => C.joins j
  | .inr (.inr (.inl j)) => C.translations j
  | .inr (.inr (.inr j)) => C.zeros.get j

include C in
theorem two_ne : (2 : ZMod p) ≠ 0 := by
  have := C.p_eq
  exact natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)

/-- All four components satisfy the row closure equation. -/
theorem closed (switch : ℕ → Bool) (j : C.Row switch) : Closed m (C.row switch j) := by
  rcases j with ⟨i,j⟩ | j | j | j
  · exact fiberRows_closed m C.two_ne _ _ _ _ _ _ _ _ _ (List.get_mem _ _)
  · have size : p = 2 * q + 1 := by have := C.p_eq; have := C.q_eq; omega
    exact Joins.closed m C.two_ne C.special.power_K _ _ size _
  · exact Translations.paper_closed m _ C.large C.p_eq C.q_eq C.two_ne C.special.power_E j
  · exact Zero.rows_closed m C.two_ne _ _ _ _ _ rfl C.params.sum _ (List.get_mem _ _)

/-- The signed choice of the distinguished zero pair as an equality in the exponent group. -/
theorem v_mem : C.v = Zero.start C.params.j ∨ C.v = -(Zero.start C.params.j + 1) := by
  have ⟨_, hj⟩ := C.params.index
  have hq := C.q_eq
  have val : (Zero.start C.params.j : Fin q).val = 2 * C.params.j + 1 :=
    Fin.val_cast_of_lt (by omega)
  rcases C.params.member with h | h
  · exact Or.inl (Fin.ext (h.trans val.symm))
  · right
    apply Fin.ext
    have ee : Zero.start C.params.j + 1 = ((2 * C.params.j + 2 : ℕ) : Fin q) :=
      (Nat.cast_add (R := Fin q) (2 * C.params.j + 1) 1).symm
    have ev : (Zero.start C.params.j + 1 : Fin q).val = 2 * C.params.j + 2 := by
      rw [ee, Fin.val_cast_of_lt (by omega)]
    have hn : Zero.start C.params.j + 1 ≠ (0 : Fin q) := Fin.val_ne_zero_iff.mp (by omega)
    rw [Fin.val_neg, ite_eq_right hn, ev]
    exact h

end Construction
end BipartiteKneser.Family
