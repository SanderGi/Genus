import KneserConstruction.FamilyTransOrder
import KneserConstruction.Coordinates

/-! # Coordinates of translation rows and their signed slot equations -/

namespace BipartiteKneser.Family.Translations

open Coordinates

variable {p q r : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable (m : Multipliers p q) (L : Layout r) (E : Fin q) (wa wb : ZMod p)

/-- The two positive translation representatives at zero-based index i. -/
def U (i : Fin r) : Frame p q := T ((i.val : ZMod p) + 2)
/-- Upper translation representative at index i. -/
def V (i : Fin r) : Frame p q := T ((r : ZMod p) + i.val + 2)

/-- Paper order Q(a,b;c,d). The first cut stores the lower mixed row, the
second cut stores the translation-only replacement, and none stores the upper mixed row. -/
noncomputable def row : Row r → Quad (Frame p q)
  | none => ⟨V (first L), X m E wa, inverse m (V (afterFirst L)), X m (-E) wb⟩
  | some i =>
    if i = first L then
      ⟨U i, X m E (-wa), U (afterSecond L), X m (-E) (-wb)⟩
    else if i = second L then
      ⟨U i, inverse m (V i), inverse m (U (afterFirst L)), V (afterSecond L)⟩
    else if i = afterSecond L then
      ⟨U i, V i, inverse m (U (next L i)), inverse m (V (next L i))⟩
    else ⟨U i, V i, V (next L i), U (next L i)⟩

/-- Canonical signed inventory. The ordinary pair selector is false for U
and true for V. The endpoint selector takes the negative then positive coordinate.
The last bit selects the inverse in either case. -/
noncomputable def label (k : Fin q) (w : ZMod p) (x : Row r × Slot) : Frame p q :=
  let a := match x.1 with
    | none => X m k (if x.2.1 then w else -w)
    | some i => if x.2.1 then V i else U i
  if x.2.2 then inverse m a else a

theorem inverse_T (c : ZMod p) : inverse m (T (q := q) c) = T (-c) := by
  simp [inverse, T, m.zero]

theorem inverse_inverse_T (c : ZMod p) :
    inverse m (inverse m (T (q := q) c)) = T c := by simp [inverse_T]

private theorem cuts_distinct :
    first L ≠ second L ∧ first L ≠ afterSecond L ∧ second L ≠ afterSecond L := by
  have := L.lower
  simp [first, second, afterSecond, Fin.ext_iff]
  omega


/-- Domain slots enumerate all signed translations and both signed E endpoint pairs at wa. -/
theorem domain_val (i : Row r) (s : Slot) :
    label m E wa (domain L (i,s)) = Quad.dom (inverse m) (row m L E wa wb i) s := by
  obtain ⟨h₁, h₂, h₃⟩ := cuts_distinct L
  obtain ⟨b,t⟩ := s
  cases i with
  | none => cases b <;> cases t <;>
      simp [label, domain, domMove, signedMove, row, Quad.dom, Equiv.swap_apply_def]
  | some i =>
    by_cases h : i = first L <;> by_cases j : i = second L <;> by_cases k : i = afterSecond L <;>
      cases b <;> cases t <;>
      simp_all [label, domain, domMove, signedMove, row, Quad.dom, Equiv.swap_apply_def,
        U, V, inverse_inverse_T]

private theorem ranMove_none (b : Bool) :
    ranMove L (none,b) = (if b then (some (first L),true) else (none,true)) := by
  cases b <;> simp [ranMove, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem ranMove_first (b : Bool) :
    ranMove L (some (first L),b) = (if b then (some (second L),false) else (none,false)) := by
  cases b <;> simp [ranMove, Equiv.Perm.mul_apply, Equiv.swap_apply_def, first_ne_second,
    (first_ne_second L).symm]

private theorem ranMove_second (b : Bool) :
    ranMove L (some (second L),b) =
      (if b then (some (first L),false) else (some (second L),true)) := by
  cases b <;> simp [ranMove, Equiv.Perm.mul_apply, Equiv.swap_apply_def, (first_ne_second L).symm]

private theorem ranMove_other {i : Fin r} (h : i ≠ first L) (j : i ≠ second L) (b : Bool) :
    ranMove L (some i,b) = (some i,b) := by
  apply List.formPerm_apply_of_notMem
  simp [h, j]

/-- Range slots use the same translations and both signed endpoint pairs at wb,
written with exponent −E as in the mixed row formulas. -/
theorem range_val (i : Row r) (s : Slot) :
    label m (-E) wb (range L (i,s)) = Quad.ran (inverse m) (row m L E wa wb i) s := by
  obtain ⟨h₁, h₂, h₃⟩ := cuts_distinct L
  obtain ⟨b,t⟩ := s
  cases i with
  | none => cases b <;> cases t <;>
      simp [label, range, transposeSlot, reverseSlot, signedMove, ranMove_none, row, Quad.ran,
        Equiv.optionCongr_apply, V, inverse_inverse_T]
  | some i =>
    by_cases h : i = first L
    · subst i
      cases b <;> cases t <;>
        simp [label, range, transposeSlot, reverseSlot, signedMove, ranMove_first, row, Quad.ran,
          Equiv.optionCongr_apply, h₁, h₂]
    by_cases j : i = second L
    · subst i
      cases b <;> cases t <;>
        simp [label, range, transposeSlot, reverseSlot, signedMove, ranMove_second, row, Quad.ran,
          Equiv.optionCongr_apply, h, h₃, U, inverse_inverse_T]
    by_cases k : i = afterSecond L
    · subst i
      cases b <;> cases t <;>
        simp [label, range, transposeSlot, reverseSlot, signedMove, ranMove_other L h j, row,
          Quad.ran, Equiv.optionCongr_apply, h, j, U, V, inverse_inverse_T]
    cases b <;> cases t <;>
      simp [label, range, transposeSlot, reverseSlot, signedMove, ranMove_other L h j, row,
        Quad.ran, Equiv.optionCongr_apply, h, j, k]

end BipartiteKneser.Family.Translations
