import KneserConstruction.FamilyChains
import KneserConstruction.CoordinateResidues
import Mathlib.Algebra.BigOperators.Fin

/-! # Partition of the connection set by exponent and coordinate -/

namespace BipartiteKneser.Family.Inventory

open Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Weight one for each admissible affine label, and zero for excluded labels. -/
def weight (m : Multipliers p q) (s : Frame p q) : Multiset (Frame p q) :=
  if separated m.power s then {s} else 0

variable (m : Multipliers p q)

/-- Reindex the entire affine group by the exponent and the centered coordinate. -/
noncomputable def chart : (Fin q × ZMod p) ≃ Frame p q := by
  apply Equiv.ofBijective (fun x => X m x.1 x.2)
  constructor
  · rintro ⟨k,w⟩ ⟨l,t⟩ h
    exact Prod.ext ((X_eq_X_iff m).mp h).1 ((X_eq_X_iff m).mp h).2
  · intro s
    obtain ⟨w, hw, _⟩ := existsUnique_X m s
    exact ⟨(s.2, w), hw⟩

theorem inventory_sum : inventory m = ∑ k, ∑ w, weight m (X m k w) := by
  classical
  have h : inventory m = ∑ s : Label m, ({s.val} : Multiset (Frame p q)) := by
    unfold inventory
    rw [← Finset.sum_multiset_singleton (Finset.univ : Finset (Label m))]
    exact map_sum (Multiset.mapAddMonoidHom Subtype.val) _ _
  rw [h]
  calc
    _ = ∑ s : Frame p q, weight m s := by
      unfold weight
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ a : Fin q × ZMod p, weight m ((chart m) a) := ((chart m).sum_comp (weight m)).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Sum over 0 and the two orientations of each positive half-range index. -/
theorem sum_signed {n t : ℕ} [NeZero n] (size : n = 2 * t + 1) {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) :
    ∑ k, f k = f 0 +
      ∑ i : Fin t, (f (Fin.ofNat n (i.val + 1)) + f (-(Fin.ofNat n (i.val + 1)))) := by
  classical
  rw [← (Equiv.optionSubtypeNe (0 : Fin n)).sum_comp f, Fintype.sum_option]
  simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
  congr 1
  rw [← (signedResidueEquiv size).sum_comp (fun k => f k.val), Fintype.sum_prod_type]
  simp [add_comm]

theorem sum_field {t : ℕ} (size : p = 2 * t + 1) {A : Type*} [AddCommMonoid A]
    (f : ZMod p → A) :
    ∑ w, f w = f 0 + ∑ i : Fin t, (f ((i.val : ZMod p) + 1) + f (-((i.val : ZMod p) + 1))) := by
  have cast (n : ℕ) : (ZMod.finEquiv p) (Fin.ofNat p n) = (n : ZMod p) := by
    cases p with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ p => rfl
  rw [← (ZMod.finEquiv p).toEquiv.sum_comp f, sum_signed size]
  change f ((ZMod.finEquiv p) 0) + ∑ i : Fin t, (f ((ZMod.finEquiv p)
    (Fin.ofNat p (i.val + 1))) + f ((ZMod.finEquiv p) (-(Fin.ofNat p (i.val + 1))))) = _
  simp only [map_zero, map_neg, cast, Nat.cast_add, Nat.cast_one]

/-- On either orientation the same exclusion test selects the entire quartet. -/
theorem quartet_weight (h₂ : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ZMod p) :
    (weight m (X m k w) + weight m (X m k (-w))) +
      (weight m (X m (-k) w) + weight m (X m (-k) (-w))) =
      if separated m.power (X m k w) then quartet m k w else 0 := by
  have h₁ := present_signs m h₂ k w
  have h₂' := present_signs m h₂ (-k) w
  simp only [weight, h₁.1, h₁.2, h₂'.2]
  cases separated m.power (X m k w) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, zero_add, quartet, pair, inverse_X' m h₂,
      neg_neg]
  ac_rfl

theorem weight_zero_pair (h₂ : (2 : ZMod p) ≠ 0) {k : Fin q} (hk : k ≠ 0) :
    weight m (X m k 0) + weight m (X m (-k) 0) = pair (inverse m) (X m k 0) := by
  have sep : separated m.power (X m k 0) = true := by
    rw [separated_X_iff m h₂]
    have hv := v_ne_zero m h₂ hk
    have hh : (1 / 2 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h₂
    exact ⟨Ne.symm hh, Ne.symm (neg_ne_zero.mpr hh), Ne.symm hv, Ne.symm (neg_ne_zero.mpr hv)⟩
  simp [weight, pair, inverse_X' m h₂, (present_signs m h₂ k 0).1, sep]

/-- The last coordinate has absolute value one half, so its entire fiber is absent. -/
theorem sep_top (h₂ : (2 : ZMod p) ≠ 0) (size : p = 2 * q + 1) (k : Fin q) :
    separated m.power (X m k (q : ZMod p)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact ((separated_X_iff m h₂ _ _).mp h).2.1 (top_fiber h₂ size)


/-- Translation coordinate reparametrization for exponent zero. -/
theorem translations : (∑ w, weight m (X m 0 w)) = ∑ c, weight m (T c) := by
  let e : ZMod p ≃ ZMod p := Equiv.ofBijective (pi m 0) (by
    constructor
    · intro w t h
      unfold pi at h
      exact mul_left_cancel₀ (one_add_mult_ne_zero m 0) (add_left_cancel h)
    · intro c
      obtain ⟨w, hw, _⟩ := existsUnique_X m (T (q := q) c)
      exact ⟨w, by simpa [T] using congrArg (fun s : Frame p q => ZMod.finEquiv p s.1) hw⟩)
  exact e.sum_comp (fun c => weight m (T c))

/-- Contribution of a fixed positive exponent and its negative, separated into
the zero coordinate and all positive coordinate pairs. -/
theorem exponent_weight (h₂ : (2 : ZMod p) ≠ 0) (size : p = 2 * q + 1)
    {k : Fin q} (hk : k ≠ 0) :
    (∑ w, weight m (X m k w)) + (∑ w, weight m (X m (-k) w)) =
      pair (inverse m) (X m k 0) +
      ∑ i : Fin (q - 1), if separated m.power (X m k ((i.val : ZMod p) + 1)) then
        quartet m k ((i.val : ZMod p) + 1) else 0 := by
  rw [sum_field size, sum_field size]
  rw [add_add_add_comm, weight_zero_pair m h₂ hk, ← Finset.sum_add_distrib]
  simp_rw [quartet_weight m h₂]
  congr 1
  let value (n : ℕ) := if separated m.power (X m k ((n : ZMod p) + 1)) then
    quartet m k ((n : ZMod p) + 1) else 0
  have hq := NeZero.pos q
  let e := finCongr (show (q - 1) + 1 = q by omega)
  change (∑ i : Fin q, value i.val) = _
  rw [← e.sum_comp (fun i => value i.val), Fin.sum_univ_castSucc]
  have endValue : value (q - 1) = 0 := by
    have eq : ((q - 1 : ℕ) : ZMod p) + 1 = (q : ZMod p) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (Nat.cast : ℕ → ZMod p) (show q - 1 + 1 = q by omega)
    simp [value, eq, sep_top m h₂ size]
  change (∑ i : Fin (q - 1), value i.val) + value (q - 1) = _
  rw [endValue, add_zero]

/-- The complete positive-coordinate partition before grouping the zero and translation blocks. -/
theorem partition {r : ℕ} (h₂ : (2 : ZMod p) ≠ 0) (size : p = 2 * q + 1)
    (expSize : q = 2 * r + 1) :
    inventory m = (∑ c, weight m (T c)) +
      (∑ i : Fin r, pair (inverse m) (X m (Fin.ofNat q (i.val + 1)) 0)) +
      ∑ w : Fin (q - 1), ∑ i : Fin r,
        if separated m.power (X m (Fin.ofNat q (i.val + 1)) ((w.val : ZMod p) + 1)) then
          quartet m (Fin.ofNat q (i.val + 1)) ((w.val : ZMod p) + 1) else 0 := by
  have pos (i : Fin r) : (Fin.ofNat q (i.val + 1)) ≠ 0 := by
    apply Fin.val_ne_zero_iff.mp
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega
  rw [inventory_sum, sum_signed expSize, translations m]
  simp_rw [exponent_weight m h₂ size (pos _)]
  rw [Finset.sum_add_distrib, ← add_assoc]
  congr 1
  rw [Finset.sum_comm]

end BipartiteKneser.Family.Inventory
