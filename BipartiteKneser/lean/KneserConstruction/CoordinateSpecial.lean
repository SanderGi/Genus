module

public import KneserConstruction.Coordinates
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Distinguished exponent pairs

Existence of the three discrete logarithms is proved for every prime in the
paper's residue class, including both branches modulo three.
-/

@[expose] public section

namespace BipartiteKneser.Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] (m : Multipliers p q)

/-- Every nonzero field element is a multiplier up to a sign. -/
theorem signed_mult (x : ZMod p) (hx : x ≠ 0) :
    ∃ k, mult m k = x ∨ -mult m k = x := by
  obtain ⟨k, a | a⟩ := m.signed ((ZMod.finEquiv p).symm x) (by simpa using hx)
  · exact ⟨k, Or.inl (by simpa [mult, Multipliers.fieldPower] using congrArg (ZMod.finEquiv p) a)⟩
  · exact ⟨k, Or.inr (by simpa [mult, Multipliers.fieldPower] using congrArg (ZMod.finEquiv p) a)⟩

/-- Squaring removes the sign ambiguity in the multiplier representation. -/
theorem exists_mult_iff {x : ZMod p} (res : p % 4 = 3) (hx : x ≠ 0) :
    (∃ k, mult m k = x) ↔ IsSquare x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact m.square k
  · exact m.exists_log res hx

/-- The multiplier singled out for N by Lemma 4.6. -/
def nValue (p : ℕ) [Fact p.Prime] : ZMod p :=
  if p % 3 = 1 then -1 / 3 else -2 / 3

/-- The three distinguished logarithms together with their defining equations. -/
structure Special (m : Multipliers p q) where
  /-- Last exponent in an ordinary coordinate-fiber chain. -/
  K : Fin q
  /-- First exponent in an ordinary coordinate-fiber chain. -/
  N : Fin q
  /-- Substitute endpoint in the two exceptional fibers. -/
  E : Fin q
  /-- The multiplier that gives the join equation `y = w - 2z`. -/
  power_K : mult m K = -1 / 2
  /-- The branch of the N multiplier selected by the prime modulo three. -/
  power_N : mult m N = nValue p
  /-- The multiplier used in the translation splice. -/
  power_E : mult m E = 4

omit [NeZero p] in
/-- Small positive numerals used in the coordinate formulas survive reduction. -/
theorem natCast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hn hp

theorem special_exists (hp : 19 ≤ p) (res : p % 8 = 3) : Nonempty (Special m) := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by decide) (by omega)
  have h₄ : (4 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 4) (by decide) (by omega)
  have s₂ : IsSquare (-2 : ZMod p) := (ZMod.exists_sq_eq_neg_two_iff (by omega)).2 (Or.inr res)
  have sK : IsSquare (-1 / 2 : ZMod p) := by
    simpa [div_eq_mul_inv] using s₂.inv
  have reciprocity := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
    (p := p) (q := 3) (by omega) (by decide) (by omega)
  obtain ⟨K, hk⟩ := m.exists_log (by omega) (div_ne_zero (neg_ne_zero.mpr one_ne_zero) h₂) sK
  obtain ⟨E, he⟩ := (exists_mult_iff m (by omega) h₄).2 ⟨2, by norm_num⟩
  suffices sN : IsSquare (nValue p) by
    have hn : nValue p ≠ 0 := by
      unfold nValue
      split
      · exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) h₃
      · exact div_ne_zero (neg_ne_zero.mpr h₂) h₃
    obtain ⟨N, hN⟩ := (exists_mult_iff m (by omega) hn).2 sN
    exact ⟨⟨K, N, E, hk, hN, he⟩⟩
  have hPrime : p.Prime := Fact.out
  have nr : p % 3 ≠ 0 := by
    intro heq
    have := (Nat.dvd_prime hPrime).mp (Nat.dvd_of_mod_eq_zero heq : 3 ∣ p)
    omega
  rw [← ZMod.natCast_mod p 3] at reciprocity
  unfold nValue
  split_ifs with h
  · have ns : ¬IsSquare (3 : ZMod p) := by
      rw [h, Nat.cast_one] at reciprocity
      exact fun hs => reciprocity.mp hs .one
    obtain ⟨k, heq | heq⟩ := signed_mult m 3 h₃
    · exact (ns (heq ▸ m.square k)).elim
    · have hs : IsSquare (-3 : ZMod p) := by
        rw [← heq, neg_neg]
        exact m.square k
      simpa [div_eq_mul_inv] using hs.inv
  · have h' : p % 3 = 2 := by omega
    rw [h'] at reciprocity
    have ns : ¬IsSquare (2 : ZMod 3) := by decide
    have sq : IsSquare (3 : ZMod p) := reciprocity.mpr ns
    exact s₂.div sq


namespace Special

variable {m} (d : Special m)

theorem unique (e : Special m) : d = e := by
  have k := m.fieldPower_injective (d.power_K.trans e.power_K.symm)
  have n := m.fieldPower_injective (d.power_N.trans e.power_N.symm)
  have a := m.fieldPower_injective (d.power_E.trans e.power_E.symm)
  cases d
  cases e
  congr

/-- Values of the excluded coordinate at the three distinguished exponents. -/
theorem values (hp : 19 ≤ p) :
    v m d.K = 3 / 2 ∧ v m d.N = (if p % 3 = 1 then 1 else 5 / 2) ∧
      v m d.E = -3 / 10 := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by decide) (by omega)
  have h₅ : (5 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 5) (by decide) (by omega)
  have h₁₀ : (10 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 10) (by decide) (by omega)
  have clear (k : Fin q) (w : ZMod p) : v m k = w ↔
      1 - mult m k = w * (2 * (1 + mult m k)) :=
    div_eq_iff (mul_ne_zero h₂ (one_add_mult_ne_zero m k))
  simp only [clear, d.power_K, d.power_N, d.power_E, nValue]
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> field_simp [h₂, h₃, h₅, h₁₀] <;> ring

/-- The reciprocal pairs of multipliers are disjoint and avoid the identity. -/
theorem distinct (hp : 19 ≤ p) :
    d.K ≠ 0 ∧ d.N ≠ 0 ∧ d.E ≠ 0 ∧
    d.K ≠ d.N ∧ d.K ≠ -d.N ∧ d.K ≠ d.E ∧ d.K ≠ -d.E ∧ d.N ≠ d.E ∧ d.N ≠ -d.E := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by decide) (by omega)
  have h₄ : (4 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 4) (by decide) (by omega)
  have small (n : ℕ) (hn : 0 < n) (hb : n < 19) : (n : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_lt hn (by omega)
  repeat' apply And.intro
  all_goals
    intro eq
    have he := congrArg (mult m) eq
    simp only [mult_zero, mult_neg, d.power_K, d.power_N, d.power_E, nValue] at he
    try split_ifs at he
  all_goals
    field_simp [h₂, h₃, h₄] at he
    have bad := sub_eq_zero.mpr he
    ring_nf at bad
    first
    | exact one_ne_zero bad
    | exact one_ne_zero (neg_eq_zero.mp bad)
    | exact small _ (by decide) (by decide) bad
    | exact small _ (by decide) (by decide) (neg_eq_zero.mp bad)

end Special
end BipartiteKneser.Coordinates
