import KneserConstruction.FamilyTransRows

/-! # Group closure for the translation replacements -/

namespace BipartiteKneser.Family.Translations

open Coordinates

variable {p q r : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable (m : Multipliers p q) (L : Layout r) (E : Fin q) (wa wb : ZMod p)

theorem compose_T (x y : ZMod p) :
    compose m.power (T (q := q) x) (T y) = T (x + y) := by
  simp [compose, T, m.zero]

private theorem mixed (h₂ : (2 : ZMod p) ≠ 0) (hE : mult m E = 4) (x y : ZMod p) :
    compose m.power (X m (-E) x) (X m E y) = T (5 * (x + y) / 4) := by
  have h₄ : (4 : ZMod p) ≠ 0 := hE ▸ mult_ne_zero m E
  apply frame_ext
  · simp only [field_compose, field_X, X_snd, pi, mult_neg, hE, T, RingEquiv.apply_symm_apply]
    field_simp [h₂, h₄]
    ring
  · simp [compose_snd, T]

/-- The three replacement rows and both ordinary row forms satisfy a c = d b.
The endpoint scalar identity is equation (2) of Section 5.1. -/
theorem closed (h₂ : (2 : ZMod p) ≠ 0) (hE : mult m E = 4)
    (balance : 4 * (L.ell : ZMod p) + 5 * (wa + wb) = 0) (i : Row r) :
    let Q := row m L E wa wb i
    compose m.power Q.a Q.c = compose m.power Q.d Q.b := by
  have h₄ : (4 : ZMod p) ≠ 0 := hE ▸ mult_ne_zero m E
  have sub₂ : 2 ≤ L.ell := by have := L.lower; omega
  have sub₄ : 4 ≤ L.ell := by have := L.lower; omega
  cases i with
  | none =>
    simp only [row, V, first, afterFirst, Nat.cast_zero, inverse_T, compose_T, mixed m E h₂ hE]
    congr 1
    apply (eq_div_iff h₄).mpr
    linear_combination -balance
  | some i =>
    simp only [row]
    split
    · rename_i h
      subst i
      simp only [U, first, afterSecond, Nat.cast_zero, Nat.cast_sub sub₄, Nat.cast_ofNat,
        compose_T, mixed m E h₂ hE]
      congr 1
      apply (eq_div_iff h₄).mpr
      linear_combination balance
    split
    · rename_i h
      subst i
      simp only [U, V, second, afterFirst, afterSecond, Nat.cast_sub sub₂, Nat.cast_sub sub₄,
        Nat.cast_ofNat, inverse_T, compose_T]
      congr 1
      ring
    split <;> simp only [U, V, inverse_T, compose_T] <;> congr 1 <;> ring

/-- The paper's value of ℓ, under the generic lower bound. -/
def paperLayout (p M : ℕ) (hM : 16 ≤ M) : Layout (2 * M) where
  ell := if p % 3 = 1 then M + 1 else 5
  lower := by split <;> omega
  upper := by split <;> omega

/-- The exceptional starting fiber for the E range. -/
def w₀ (p q : ℕ) : ℕ := if p % 3 = 1 then 1 else q - 2

omit [NeZero p] [NeZero q] in
theorem paper_balance {M : ℕ} (hM : 16 ≤ M) (hp : p = 8 * M + 3) (hq : q = 4 * M + 1) :
    4 * ((paperLayout p M hM).ell : ZMod p) +
      5 * (((q - 1 : ℕ) : ZMod p) + (w₀ p q : ZMod p)) = 0 := by
  have rel : (8 : ZMod p) * M + 3 = 0 := by
    exact_mod_cast (show ((8 * M + 3 : ℕ) : ZMod p) = 0 by rw [← hp, ZMod.natCast_self])
  have hq₁ : 1 ≤ q := by omega
  have hq₂ : 2 ≤ q := by omega
  have qcast : (q : ZMod p) = 4 * M + 1 := by
    simpa using congrArg (Nat.cast : ℕ → ZMod p) hq
  by_cases h : p % 3 = 1
  · simp only [paperLayout, w₀, ite_eq_left h, Nat.cast_sub hq₁, Nat.cast_add, Nat.cast_one, qcast]
    linear_combination 3 * rel
  · simp only [paperLayout, w₀, ite_eq_right h, Nat.cast_sub hq₁, Nat.cast_sub hq₂,
      Nat.cast_one, Nat.cast_ofNat, qcast]
    linear_combination 5 * rel

/-- Closure with the construction's numerical parameters substituted. -/
theorem paper_closed {M : ℕ} (hM : 16 ≤ M) (hp : p = 8 * M + 3) (hq : q = 4 * M + 1)
    (h₂ : (2 : ZMod p) ≠ 0) (hE : mult m E = 4) (i : Row (2 * M)) :
    let Q := row m (paperLayout p M hM) E ((q - 1 : ℕ) : ZMod p) (w₀ p q) i
    compose m.power Q.a Q.c = compose m.power Q.d Q.b :=
  closed m _ E _ _ h₂ hE (paper_balance hM hp hq) i

end BipartiteKneser.Family.Translations
