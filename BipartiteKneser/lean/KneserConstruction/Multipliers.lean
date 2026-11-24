module

public import BipartiteKneser.Rotation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The odd-order affine action

For p = 3 modulo 4 the square multipliers give one orientation to each
nonzero difference. This gives the simply transitive frame chart of Section 2
before choosing any cyclic neighbor order.
-/

public section

namespace BipartiteKneser

/-- The powers of a square generator and the signed decomposition of differences. -/
structure Multipliers (p q : ℕ) [NeZero p] [NeZero q] where
  /-- Square multiplier at each exponent. -/
  power : Fin q → Fin p
  /-- Exponent zero. -/
  zero : power 0 = 1
  /-- Addition of exponents. -/
  add : ∀ k l, power (k + l) = power k * power l
  /-- Distinct exponents give distinct multipliers. -/
  injective : Function.Injective power
  /-- The multipliers are nonzero. -/
  nonzero : ∀ k, power k ≠ 0
  /-- A multiplier is never the negative of a multiplier. -/
  ne_neg : ∀ k l, power k ≠ -power l
  /-- Every nonzero field element has a signed representation. -/
  signed : ∀ x : Fin p, x ≠ 0 → ∃ k, power k = x ∨ -power k = x
  /-- The field elements represented without a sign are squares. -/
  square : ∀ k, IsSquare (ZMod.finEquiv p (power k))

namespace Multipliers

/-- Existence of the multiplier system for all primes p = 3 modulo 4. -/
theorem exists_of_prime (p q : ℕ) [Fact p.Prime] [NeZero p] [NeZero q]
    (size : p = 2 * q + 1) (residue : p % 4 = 3) : Nonempty (Multipliers p q) := by
  classical
  obtain ⟨g, gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have ord : orderOf g = 2 * q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers gen, Nat.card_eq_fintype_card, ZMod.card_units]
    omega
  let u := g ^ 2
  have ordU : orderOf u = q := by
    change orderOf (g ^ 2) = q
    rw [orderOf_pow, ord, Nat.gcd_eq_right (dvd_mul_right ..)]
    omega
  let a (k : Fin q) := u ^ k.val
  have inj : Function.Injective a := by
    intro k l he
    apply Fin.ext
    simpa only [ordU, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt] using pow_inj_mod.mp he
  have sq (k : Fin q) : IsSquare (a k : ZMod p) := by
    refine ⟨(g : ZMod p) ^ k.val, ?_⟩
    simp [a, u, ← pow_mul, ← pow_two, Nat.mul_comm]
  have opposite (k l : Fin q) : a k ≠ -a l := by
    intro he
    have eq : (a k : ZMod p) = -(a l : ZMod p) := congrArg Units.val he
    have bad : IsSquare (-1 : ZMod p) := by
      simpa [eq] using (sq k).div (sq l)
    exact (FiniteField.isSquare_neg_one_iff.mp bad) (by simpa using residue)
  let signedPower (x : Bool × Fin q) := if x.1 then -(a x.2) else a x.2
  have bij : Function.Bijective signedPower := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, ?_⟩
    · rintro ⟨s, k⟩ ⟨t, l⟩ he
      cases s <;> cases t
      · exact Prod.ext rfl (inj he)
      · exact (opposite k l he).elim
      · exact (opposite l k he.symm).elim
      · exact Prod.ext rfl (inj (neg_injective he))
    · rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, ZMod.card_units]
      omega
  let e := (ZMod.finEquiv p).symm
  refine ⟨fun k => e (a k), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a, e]
  · intro k l
    have hm := pow_mod_orderOf u (k.val + l.val)
    rw [ordU] at hm
    change e ((u ^ (k + l).val : (ZMod p)ˣ) : ZMod p) = _
    rw [Fin.val_add, hm, pow_add, Units.val_mul, map_mul]
  · intro k l he
    exact inj (Units.ext (e.injective he))
  · intro k hk
    exact (a k).ne_zero ((map_eq_zero_iff e e.injective).mp hk)
  · intro k l he
    apply opposite k l
    apply Units.ext
    apply e.injective
    simpa using he
  · intro x hx
    have hx' : ZMod.finEquiv p x ≠ 0 := by simpa using hx
    obtain ⟨⟨s, k⟩, he⟩ := bij.2 (Units.mk0 _ hx')
    have eq := congrArg (fun b : (ZMod p)ˣ => e (b : ZMod p)) he
    cases s
    · exact ⟨k, Or.inl (by simpa [signedPower, e] using eq)⟩
    · exact ⟨k, Or.inr (by simpa [signedPower, e] using eq)⟩
  · intro k
    simpa [e] using sq k

variable {p q d : ℕ} [NeZero p] [NeZero q]

/-- The multiplier as a field element. -/
noncomputable def fieldPower (m : Multipliers p q) (k : Fin q) : ZMod p :=
  ZMod.finEquiv p (m.power k)

@[simp] theorem fieldPower_zero (m : Multipliers p q) : m.fieldPower 0 = 1 := by
  simp [fieldPower, m.zero]

theorem fieldPower_add (m : Multipliers p q) (k l : Fin q) :
    m.fieldPower (k + l) = m.fieldPower k * m.fieldPower l := by
  simp [fieldPower, m.add]

@[simp] theorem fieldPower_ne_zero (m : Multipliers p q) (k : Fin q) : m.fieldPower k ≠ 0 := by
  simpa [fieldPower] using m.nonzero k

theorem fieldPower_injective (m : Multipliers p q) : Function.Injective m.fieldPower :=
  (ZMod.finEquiv p).injective.comp m.injective

theorem fieldPower_neg [Fact p.Prime] (m : Multipliers p q) (k : Fin q) :
    m.fieldPower (-k) = (m.fieldPower k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp [← m.fieldPower_add]

theorem fieldPower_sub [Fact p.Prime] (m : Multipliers p q) (k l : Fin q) :
    m.fieldPower (k - l) = m.fieldPower k / m.fieldPower l := by
  rw [sub_eq_add_neg, m.fieldPower_add, m.fieldPower_neg, div_eq_mul_inv]

/-- Every nonzero square has a logarithm in the odd-order multiplier subgroup. -/
theorem exists_log [Fact p.Prime] (m : Multipliers p q) (residue : p % 4 = 3)
    {x : ZMod p} (hx : x ≠ 0) (square : IsSquare x) : ∃ k, m.fieldPower k = x := by
  let e := ZMod.finEquiv p
  obtain ⟨k, pos | neg⟩ := m.signed (e.symm x) (by simpa [e] using hx)
  · exact ⟨k, by simpa [fieldPower, e] using congrArg e pos⟩
  · have he : -m.fieldPower k = x := by simpa [fieldPower, e] using congrArg e neg
    have bad := square.div (m.square k)
    change IsSquare (x / m.fieldPower k) at bad
    rw [← he, neg_div, div_self (m.fieldPower_ne_zero k)] at bad
    exact ((FiniteField.isSquare_neg_one_iff.mp bad) (by simpa using residue)).elim

private theorem points_inj (m : Multipliers p q) (c : BaseCycle p q d)
    (scale : c.scale = m.power) {g s : Frame p q} (he : c.sortedPoints g = c.sortedPoints s) :
    g = s := by
  obtain ⟨a, k⟩ := g
  obtain ⟨b, l⟩ := s
  simp only [BaseCycle.sortedPoints, BaseCycle.points, scale] at he
  split at he <;> split at he <;> simp only [Prod.mk.injEq] at he
  all_goals first
    | exact Prod.ext (by grind) (m.injective (by grind))
    | exact (m.ne_neg k l (by grind)).elim

private theorem points_onto (m : Multipliers p q) (c : BaseCycle p q d)
    (scale : c.scale = m.power) (a b : Fin p) (lt : a < b) :
    ∃ g, c.sortedPoints g = (a,b) := by
  have ne : b - a ≠ 0 := by grind
  obtain ⟨k, eq | eq⟩ := m.signed _ ne
  · refine ⟨(a,k), ?_⟩
    simp [BaseCycle.sortedPoints, BaseCycle.points, scale, eq, lt]
  · refine ⟨(b,k), ?_⟩
    have e : b + m.power k = a := by grind
    simp [BaseCycle.sortedPoints, BaseCycle.points, scale, e, Fin.not_lt.mpr lt.le]

/-- The frame label is a bijection onto the increasing two-subsets for every
choice of the cyclic neighbor order using these multipliers. -/
noncomputable def chart (m : Multipliers p q) (c : BaseCycle p q d) (scale : c.scale = m.power) :
    c.Chart := by
  classical
  have inc (g : Frame p q) : (c.sortedPoints g).1 < (c.sortedPoints g).2 := by
    have nz := m.nonzero g.2
    simp only [BaseCycle.sortedPoints, BaseCycle.points, scale]
    split <;> dsimp <;> grind
  let decode (a b : Fin p) : Frame p q :=
    if lt : a < b then (points_onto m c scale a b lt).choose else (0,0)
  have right (a b : Fin p) (lt : a < b) : c.sortedPoints (decode a b) = (a,b) := by
    simpa [decode, lt] using (points_onto m c scale a b lt).choose_spec
  exact ⟨decode, inc, fun g => points_inj m c scale (right _ _ (inc g)), right⟩

end Multipliers
end BipartiteKneser
