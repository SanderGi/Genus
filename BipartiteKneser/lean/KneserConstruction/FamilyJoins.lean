module

public import BipartiteKneser.FiberJoins
public import KneserConstruction.FamilyLedger
public import KneserConstruction.Coordinates

/-!
# The K-to-N joining rows

A joining row supplies one inverse pair from each of its two signed outputs.
The inverse lookup in the integer table proves a bijection from these columns
to the signed non-missing fibers. Summing over that bijection counts every
required N inverse pair with multiplicity one.
-/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Family.Joins

open FiberJoins Coordinates

/-- All positive nonzero, non-excluded fibers except the one missing N. -/
abbrev Present (c : Case) (q : ℕ) :=
  {i : Fin (q - 1) // (i.val : ℤ) + 1 ≠ missing c q}

/-- Signed coordinate for a present N inverse pair. -/
def signed {c : Case} {q : ℕ} (i : Present c q × Bool) : ℤ :=
  if i.2 then -(i.1.val.val + 1 : ℤ) else (i.1.val.val + 1 : ℤ)

private theorem signed_injective {c : Case} {q : ℕ} : Function.Injective (@signed c q) := by
  rintro ⟨⟨⟨i, hi⟩, hmi⟩, s⟩ ⟨⟨⟨j, hj⟩, hmj⟩, t⟩ eq
  cases s <;> cases t <;> simp_all [signed] <;> omega

private theorem required_signed {c : Case} {q : ℕ} (i : Present c q × Bool) :
    Required c q (signed i) := by
  rcases i with ⟨⟨⟨i, hi⟩, hm⟩, s⟩
  change (i : ℤ) + 1 ≠ missing c q at hm
  have hq : 2 ≤ (q : ℤ) := by omega
  have hn : 0 ≤ missing c q := by cases c <;> simp [missing]; omega
  cases s <;> simp only [signed, Required, ite_true, Bool.false_eq_true, ite_false] <;> omega

private def decode {c : Case} {q : ℕ} (t : ℤ) (ht : Required c q t) : Present c q × Bool :=
  (⟨⟨t.natAbs - 1, by obtain ⟨_, _, _, _, _⟩ := ht; omega⟩, by
      obtain ⟨_, _, _, _, _⟩ := ht
      dsimp
      omega⟩, decide (t < 0))

private theorem signed_decode {c : Case} {q : ℕ} (t : ℤ) (ht : Required c q t) :
    signed (decode t ht) = t := by
  obtain ⟨_, _, _, _, _⟩ := ht
  simp only [signed, decode, decide_eq_true_eq]
  split <;> omega

/-- Paper row number for a zero-based index. -/
def number {q : ℕ} (i : Fin (q - 2)) : ℤ := i.val + 1

/-- The two columns of all joining rows enumerate exactly the signed N targets. -/
@[no_expose] def columns (c : Case) (q : ℕ) (size : InRange c q) :
    (Fin (q - 2) × Bool) ≃ (Present c q × Bool) where
  toFun i := decode (target c q (number i.1) i.2)
    (source_target c size (by dsimp [number]; omega) (by have := i.1.isLt; dsimp [number]; omega)
      i.2).1
  invFun j := (⟨(source c q (signed j)).1.toNat - 1, by
    have := target_source c size (required_signed j)
    omega⟩, (source c q (signed j)).2)
  left_inv i := by
    have h := (source_target c size (w := number i.1) (by dsimp [number]; omega)
      (by have := i.1.isLt; dsimp [number]; omega) i.2).2
    simp only [signed_decode, h]
    apply Prod.ext _ rfl
    apply Fin.ext
    dsimp [number]
  right_inv j := by
    apply signed_injective
    rw [signed_decode]
    have ht := target_source c size (required_signed j)
    convert ht.2.2 using 2
    dsimp [number]
    omega

theorem signed_columns (c : Case) (q : ℕ) (size : InRange c q) (i : Fin (q - 2) × Bool) :
    signed (columns c q size i) = target c q (number i.1) i.2 := by
  dsimp only [columns, Equiv.coe_fn_mk]
  apply signed_decode

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- The row with inputs K at both signs of w and outputs N at the table entries. -/
def row (m : Multipliers p q) (K N : Fin q) (c : Case) (i : Fin (q - 2)) :
    Quad (Frame p q) :=
  let w := number i
  ⟨X m K (w : ZMod p), X m K (-(w : ZMod p)),
    X m N (target c q w false : ℤ), X m N (target c q w true : ℤ)⟩

omit [NeZero p] [NeZero q] in
theorem relation (c : Case) (hpq : p = 2 * q + 1) (w : ℤ) :
    (target c q w false : ZMod p) = (w : ZMod p) - 2 * (target c q w true : ZMod p) := by
  have zero : ((2 * (q : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
    have eq : 2 * (q : ℤ) + 1 = (p : ℤ) := by omega
    rw [eq]
    simp
  rcases closure c (q : ℤ) w with h | h | h
  all_goals
    have h' := congrArg (Int.cast : ℤ → ZMod p) h
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sub] at h' zero
    try simp only [zero, add_zero, sub_zero] at h'
    dsimp [target]
    linear_combination h'

theorem closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) {K : Fin q}
    (hK : mult m K = -1 / 2) (N : Fin q) (c : Case) (hpq : p = 2 * q + 1) (i : Fin (q - 2)) :
    compose m.power (row m K N c i).a (row m K N c i).c =
      compose m.power (row m K N c i).d (row m K N c i).b := by
  dsimp only [row]
  rw [relation c hpq]
  exact transition_row m h2 hK N _ _

/-- The columns' signed coverage is an identity of multisets of affine frames. -/
theorem ranges (m : Multipliers p q) (K N : Fin q) (c : Case) (size : InRange c q) :
    (∑ i, (row m K N c i).ranBag (inverse m)) =
      ∑ i : Present c q, (pair (inverse m) (X m N ((i.val.val + 1 : ℤ) : ZMod p)) +
        pair (inverse m) (X m N (-((i.val.val + 1 : ℤ) : ZMod p)))) := by
  let f (t : ℤ) := pair (inverse m) (X m N (t : ZMod p))
  calc
    _ = ∑ i : Fin (q - 2) × Bool, f (target c q (number i.1) i.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fintype.sum_bool, Quad.ranBag, row, f]
      ac_rfl
    _ = ∑ i : Present c q × Bool, f (signed i) := by
      simpa only [signed_columns] using (columns c q size).sum_comp (fun j => f (signed j))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fintype.sum_bool, signed, Bool.false_eq_true, ite_false, ite_true, f, Int.cast_neg]
      ac_rfl

end BipartiteKneser.Family.Joins
