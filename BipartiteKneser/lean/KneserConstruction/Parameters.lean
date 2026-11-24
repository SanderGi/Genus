module

public import KneserConstruction.Attachment
public import KneserConstruction.Multipliers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The zero-coordinate attachment parameters of Lemma 5.5 -/

public section

namespace BipartiteKneser.Parameters

variable {p q : ℕ} [Fact p.Prime] [NeZero p] [NeZero q]

/-- Exponents used in the zero-coordinate attachment. The final alternative
identifies the member of the j - th inverse pair used by the splice. -/
structure Exponents (m : Multipliers p q) (K N E : Fin q) where
  /-- First exponent at the attachment. -/
  a : Fin q
  /-- Second exponent at the attachment. -/
  b : Fin q
  /-- Index of the distinguished zero-coordinate pair. -/
  j : ℕ
  /-- Translation closure equation. -/
  sum : m.fieldPower a + m.fieldPower b = -2
  /-- The two exponents belong to different inverse pairs. -/
  distinct : a ≠ b ∧ a ≠ -b
  /-- The attachment uses neither the identity nor a distinguished pair. -/
  avoid : ∀ k ∈ [0, K, -K, N, -N, E, -E], a ≠ k ∧ b ≠ k
  /-- Parity and range of the distinguished exponent. -/
  range : (1 + a - b).val % 2 = 1 ∧ 9 ≤ (1 + a - b).val ∧ (1 + a - b).val ≤ q - 10
  /-- The distinguished pair lies strictly after the first four pairs. -/
  index : 4 ≤ j ∧ j < (q - 1) / 4
  /-- Identification with one of the two exponents of this pair. -/
  member : (1 + a - b).val = 2 * j + 1 ∨ (1 + a - b).val = q - (2 * j + 2)

private def forbidden (q : ℕ) : List ℕ := [2, 4, 6, q - 9, q - 7, q - 5, q - 3, q - 1]

private theorem properties_of_even {q n : ℕ} (hq : q % 4 = 1) (large : 65 ≤ q) (lt : n < q)
    (pos : n ≠ 0) (even : n % 2 = 0) (allowed : n ∉ forbidden q) :
    (n + 1) % 2 = 1 ∧ 9 ≤ n + 1 ∧ n + 1 ≤ q - 10 ∧
    ∃ j, (4 ≤ j ∧ j < (q - 1)/4) ∧ (n + 1 = 2 * j + 1 ∨ n + 1 = q - (2 * j + 2)) := by
  simp [forbidden] at allowed
  refine ⟨by omega, by omega, by omega, ?_⟩
  by_cases h : n / 2 < (q - 1)/4
  · exact ⟨n / 2, ⟨by omega, h⟩, Or.inl (by omega)⟩
  · exact ⟨(q - n - 3)/2, ⟨by omega, by omega⟩, Or.inr (by omega)⟩

/-- Existence of the attachment in Lemma 5.5 for every admissible prime at least 131. -/
theorem exists_exponents (m : Multipliers p q) (K N E : Fin q)
    (size : p = 2 * q + 1) (large : 131 ≤ p) (residue : p % 8 = 3) :
    Nonempty (Exponents m K N E) := by
  classical
  have largeQ : 65 ≤ q := by omega
  have modQ : q % 4 = 1 := by omega
  have notSquare : ¬IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
    omega
  have : NeZero (2 : ZMod p) := ⟨by
    intro eq
    have h : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using eq
    have := (ZMod.natCast_eq_natCast_iff 2 0 p).mp h
    change 2 % p = 0 % p at this
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 2 < p)] at this
    contradiction⟩
  let special : List (Fin q) := [0, K, -K, N, -N, E, -E]
  let vals := (special.map m.fieldPower).toFinset
  let ratio (n : ℕ) := m.fieldPower (Fin.ofNat q n)
  let ratios := ((forbidden q).map ratio).toFinset
  obtain ⟨A, B, total, nA, nB, sqA, sqB, av, bv, ab, ba⟩ :=
    Attachment.exists_square_pair (F := ZMod p) (by simpa using large)
      ((ZMod.exists_sq_eq_neg_two_iff (by omega)).mpr (Or.inr residue)) vals ratios
      (by exact (List.toFinset_card_le _).trans_eq (by simp [special]))
      (by exact (List.toFinset_card_le _).trans_eq (by simp [forbidden]))
      (by simp [vals, m.fieldPower_ne_zero])
      (by simp [ratios, ratio])
  obtain ⟨a, rfl⟩ := m.exists_log (by omega) nA sqA
  obtain ⟨b, rfl⟩ := m.exists_log (by omega) nB sqB
  have diff : a ≠ b := by
    rintro rfl
    have h : (2 : ZMod p) * (m.fieldPower a + 1) = 0 := by
      linear_combination total
    have ha := (mul_eq_zero.mp h).resolve_left two_ne_zero
    exact notSquare ((eq_neg_of_add_eq_zero_left ha) ▸ sqA)
  have inv : a ≠ -b := by
    rintro rfl
    rw [m.fieldPower_neg] at total
    have hv : (m.fieldPower b + 1)^2 = 0 := by
      field_simp at total
      linear_combination total
    have he := eq_neg_of_add_eq_zero_left (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp hv)
    exact notSquare (he ▸ sqB)
  have arrange (x y : Fin q) (sum : m.fieldPower x + m.fieldPower y = -2)
      (ne : x ≠ y) (opp : x ≠ -y) (hX : m.fieldPower x ∉ vals) (hY : m.fieldPower y ∉ vals)
      (hr : m.fieldPower x / m.fieldPower y ∉ ratios) (even : (x - y).val % 2 = 0) :
      Nonempty (Exponents m K N E) := by
    have avoid : (x - y).val ∉ forbidden q := by
      intro hn
      apply hr
      rw [← m.fieldPower_sub]
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨(x - y).val, hn, by simp [ratio]⟩
    have nz : (x - y).val ≠ 0 := by simpa using (sub_ne_zero.mpr ne : x - y ≠ 0)
    obtain ⟨odd, low, high, j, index, member⟩ :=
      properties_of_even modQ largeQ (x - y).isLt nz even avoid
    have hv : (1 + x - y).val = (x - y).val + 1 := by
      rw [add_sub_assoc, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < q),
        Nat.mod_eq_of_lt (by omega)]
      omega
    refine ⟨x, y, j, sum, ⟨ne, opp⟩, ?_, hv ▸ ⟨odd, low, high⟩, index, hv ▸ member⟩
    intro k hk
    have mem : m.fieldPower k ∈ vals := List.mem_toFinset.mpr (List.mem_map_of_mem hk)
    exact ⟨fun eq => hX (eq ▸ mem), fun eq => hY (eq ▸ mem)⟩
  by_cases even : (a - b).val % 2 = 0
  · exact arrange a b total diff inv av bv ab even
  · apply arrange b a (by rw [add_comm]; exact total) (Ne.symm diff)
      (fun eq => inv (by simpa using congrArg Neg.neg eq.symm)) bv av ba
    have h : b - a = -(a - b) := (neg_sub _ _).symm
    rw [h, Fin.val_neg, ite_eq_right (sub_ne_zero.mpr diff)]
    have := (a - b).isLt
    omega

end BipartiteKneser.Parameters
