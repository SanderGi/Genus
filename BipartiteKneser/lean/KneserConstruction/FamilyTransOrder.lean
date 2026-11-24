module

public import KneserConstruction.FamilyCore
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.List.FinRange

/-! # The translation cycle and the signed slot permutations of Construction 5.2 -/

@[expose] public section

namespace BipartiteKneser.Family.Translations

/-- The bounds on the paper's distinguished translation parameter. -/
structure Layout (r : ℕ) where
  /-- Translation parameter ℓ of Construction 5.2. -/
  ell : ℕ
  lower : 5 ≤ ell
  upper : ell + 1 ≤ r

variable {r : ℕ} (L : Layout r)

/-- Indices are zero-based, so these four cuts stand for 1, ℓ+1, ℓ−1, ℓ−3. -/
def first : Fin r := ⟨0, by have := L.lower; have := L.upper; omega⟩
/-- Successor of the first reserved index in the chosen cyclic order. -/
def afterFirst : Fin r := ⟨L.ell, by have := L.upper; omega⟩
/-- Second index whose translation row is replaced. -/
def second : Fin r := ⟨L.ell - 2, by have := L.upper; omega⟩
/-- Successor of the second replaced index. -/
def afterSecond : Fin r := ⟨L.ell - 4, by have := L.upper; omega⟩

/-- The four prescribed indices at the start of the translation order. -/
def cuts := [first L, afterFirst L, second L, afterSecond L]

theorem cuts_nodup : (cuts L).Nodup := by
  have := L.lower
  simp [cuts, first, afterFirst, second, afterSecond, Fin.ext_iff]
  omega

/-- The four reserved indices precede all other indices in increasing order. -/
def order := cuts L ++ (List.finRange r).filter (fun i => i ∉ cuts L)

theorem order_nodup : (order L).Nodup := by
  rw [order, List.nodup_append]
  exact ⟨cuts_nodup L, (List.nodup_finRange r).filter _, by simp; grind⟩

theorem mem_order (i : Fin r) : i ∈ order L := by
  by_cases h : i ∈ cuts L <;> simp [order, h]

theorem order_length : (order L).length = r := by
  have h : (order L).toFinset = Finset.univ := Finset.ext (by simp [mem_order])
  rw [← List.toFinset_card_of_nodup (order_nodup L), h, Finset.card_univ, Fintype.card_fin]

/-- Successor including the wrap from the last ordinary index to the first cut. -/
def next := (order L).formPerm

@[simp] theorem next_first : next L (first L) = afterFirst L :=
  List.formPerm_apply_head _ _ _ (order_nodup L)

@[simp] theorem next_second : next L (second L) = afterSecond L := by
  exact List.formPerm_apply_lt_getElem (order L) (order_nodup L) 2 (by simp [order, cuts])

theorem first_ne_second : first L ≠ second L := by
  have := L.lower
  simp [first, second, Fin.ext_iff]
  omega

/-- A regular row or the additional endpoint row of Lemma 5.1. -/
abbrev Row (r : ℕ) := Option (Fin r)

/-- A translation row address together with its inverse-pair selector. -/
abbrev PairAddr (r : ℕ) := Row r × Bool

/-- Exchange one translation pair with the exceptional E pair in the domain. -/
def domMove := Equiv.swap (some (first L), true) (none, false)

/-- Range pair addresses before advancing to the successor translation index. -/
def ranMove : Equiv.Perm (PairAddr r) :=
  [(some (first L), false), (none, false), (none, true), (some (first L), true),
    (some (second L), false), (some (second L), true)].formPerm

/-- Lift a permutation of pairs to the individual labels, reversing selected orientations. -/
def signedMove (move : Equiv.Perm (PairAddr r)) (flip : PairAddr r → Bool) :
    Equiv.Perm (Row r × Slot) where
  toFun x := (let y := move (x.1, x.2.1); (y.1, y.2, xor x.2.2 (flip (x.1, x.2.1))))
  invFun x := (let y := move.symm (x.1, x.2.1); (y.1, y.2, xor x.2.2 (flip y)))
  left_inv := by rintro ⟨i,b,s⟩; simp
  right_inv := by rintro ⟨i,b,s⟩; simp

/-- The domain exchanges the upper translation at 1 with the first endpoint,
and reverses the upper translation at ℓ−1. -/
def domain := signedMove (domMove L) (fun x => decide (x = (some (second L), true)))

/-- Exchange pair and orientation bits to read a quadruple from the range side. -/
def transposeSlot : Equiv.Perm (Row r × Slot) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)

/-- Complement both slot bits at the reversed translation row. -/
def reverseSlot (i : Fin r) : Equiv.Perm (Row r × Slot) where
  toFun x := if x.1 = some i then (x.1, !x.2.1, !x.2.2) else x
  invFun x := if x.1 = some i then (x.1, !x.2.1, !x.2.2) else x
  left_inv := by rintro ⟨j,b,s⟩; by_cases h : j = some i <;> simp [h]
  right_inv := by rintro ⟨j,b,s⟩; by_cases h : j = some i <;> simp [h]

/-- The first range bit chooses inversion and the second selects d or c.
After redistributing the replacement pairs, advance ordinary addresses by one edge. -/
def range : Equiv.Perm (Row r × Slot) :=
  ((transposeSlot.trans (reverseSlot (afterSecond L))).trans
    (signedMove (ranMove L) (fun x =>
      decide (x = (some (second L), true) ∨ x = (none, true))))).trans
    (Equiv.prodCongr (Equiv.optionCongr (next L)) (Equiv.refl _))

end BipartiteKneser.Family.Translations
