module

public import KneserConstruction.Inventory
public import KneserConstruction.FamilyTransRows
public import KneserConstruction.FamilyZeroRows

/-! # The translation and zero-coordinate summands of the connection set -/

@[expose] public section

namespace BipartiteKneser.Family.Inventory

open Coordinates

variable {p q r M : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] (m : Multipliers p q)

/-- Away from 0 and ±1 both directions of a translation occur. -/
theorem translation_pair {n : ℕ} (lo : 2 ≤ n) (hi : n + 1 < p) :
    weight m (T (n : ZMod p)) + weight m (T (-(n : ZMod p))) =
      pair (inverse m) (T (n : ZMod p)) := by
  have nz {a : ℕ} (ha : 0 < a) (hb : a < p) : (a : ZMod p) ≠ 0 :=
    fun h => Nat.not_dvd_of_pos_of_lt ha hb ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have h0 : (n : ZMod p) ≠ 0 := nz (by omega) (by omega)
  have h1 : (n : ZMod p) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_one'' (by omega)] at hh
    omega
  have hn : (n : ZMod p) ≠ -1 := by
    intro h
    apply nz (a := n + 1) (by omega) hi
    push_cast
    simp [h]
  have hp : separated m.power (T (n : ZMod p)) = true :=
    (separated_T_iff m _).mpr ⟨h0, h1, hn⟩
  have hm : separated m.power (T (-(n : ZMod p))) = true := by
    rw [separated_T_iff]
    exact ⟨neg_ne_zero.mpr h0, fun h => hn (by simpa using congrArg Neg.neg h),
      neg_injective.ne h1⟩
  simp [weight, hp, hm, pair, Translations.inverse_T]

theorem translation_blocks (size : p = 2 * q + 1) (eq : q = 2 * r + 1) :
    (∑ c, weight m (T c)) =
      ∑ i : Fin r, (pair (inverse m) (Translations.U i) +
        pair (inverse m) (Translations.V i)) := by
  let g (n : ℕ) := weight m (T (n : ZMod p)) + weight m (T (-(n : ZMod p)))
  have nil0 : weight m (T 0) = 0 := by simp [weight, separated_T_iff]
  have nil1 : g 1 = 0 := by
    have ha : separated m.power (T (q := q) (1 : ZMod p)) = false := by
      simp [Bool.eq_false_iff, separated_T_iff]
    have hb : separated m.power (T (q := q) (-1 : ZMod p)) = false := by
      simp [Bool.eq_false_iff, separated_T_iff]
    simp [g, weight, ha, hb]
  rw [sum_field size, nil0, zero_add]
  have cast (n : ℕ) : (n : ZMod p) + 1 = ((n + 1 : ℕ) : ZMod p) := by push_cast; rfl
  simp_rw [cast]
  change (∑ i : Fin q, g (i.val + 1)) = _
  rw [← (finCongr eq.symm).sum_comp (fun i => g (i.val + 1)), Fin.sum_univ_succ]
  change g 1 + (∑ i : Fin (2 * r), g (i.val + 2)) = _
  rw [nil1, zero_add]
  let e : Fin r ⊕ Fin r ≃ Fin (2*r) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.sum_comp (fun i => g (i.val + 2)), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change g (i.val + 2) + g (r + i.val + 2) = _
  have := i.isLt
  dsimp only [g]
  rw [translation_pair m (by omega) (by omega), translation_pair m (by omega) (by omega)]
  simp [Translations.U, Translations.V, Nat.cast_add]

theorem zero_blocks (rSize : r = 2 * M) :
    (∑ i : Fin r, pair (inverse m) (X m (Fin.ofNat q (i.val + 1)) 0)) =
    ∑ j : Fin M, Zero.block m (Fin.ofNat q (2 * j.val + 1)) := by
  let g (i : Fin r) := pair (inverse m) (X m (Fin.ofNat q (i.val + 1)) 0)
  let e : Fin M × Fin 2 ≃ Fin r := finProdFinEquiv.trans (finCongr (by omega))
  change (∑ i, g i) = _
  rw [← e.sum_comp g, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  change pair _ (X m (Fin.ofNat q (0 + 2 * j.val + 1)) 0) +
    pair _ (X m (Fin.ofNat q (1 + 2 * j.val + 1)) 0) = _
  simp only [Nat.zero_add, Zero.block, Zero.Z]
  congr 3
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod, Nat.add_comm]

end BipartiteKneser.Family.Inventory
