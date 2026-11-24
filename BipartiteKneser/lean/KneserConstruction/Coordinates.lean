import KneserConstruction.Multipliers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Affine coordinates for the connection set

The first coordinate is calculated in the prime field. The resulting frame
uses the existing `Fin` representation, so the formulas apply to `compose`
and `separated` directly.
-/

noncomputable section

namespace BipartiteKneser.Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Square multiplier in field coordinates. -/
abbrev mult (m : Multipliers p q) := m.fieldPower

/-- Translation component of the centered coordinate frame. -/
def pi (m : Multipliers p q) (k : Fin q) (w : ZMod p) : ZMod p :=
  (1 - mult m k) / 2 + (1 + mult m k) * w

/-- Affine frame of Definition 4.1. -/
def X (m : Multipliers p q) (k : Fin q) (w : ZMod p) : Frame p q :=
  ((ZMod.finEquiv p).symm (pi m k w), k)

/-- Translation by the given field element. -/
def T (c : ZMod p) : Frame p q := ((ZMod.finEquiv p).symm c, 0)

/-- Inversion with the chosen multiplier system. -/
def inv (m : Multipliers p q) (s : Frame p q) : Frame p q :=
  (-(m.power (-s.2) * s.1), -s.2)

/-- Missing coordinate in the exponent slice. -/
def v (m : Multipliers p q) (k : Fin q) : ZMod p :=
  (1 - mult m k) / (2 * (1 + mult m k))

variable (m : Multipliers p q)

theorem mult_zero : mult m 0 = 1 := m.fieldPower_zero
@[simp] theorem mult_add (k l : Fin q) : mult m (k + l) = mult m k * mult m l :=
  m.fieldPower_add k l

theorem mult_ne_zero (k : Fin q) : mult m k ≠ 0 := m.fieldPower_ne_zero k

omit [Fact p.Prime] in
theorem mult_injective : Function.Injective (mult m) :=
  m.fieldPower_injective

theorem one_add_mult_ne_zero (k : Fin q) : 1 + mult m k ≠ 0 := by
  intro he
  apply m.ne_neg k 0
  apply (ZMod.finEquiv p).injective
  rw [map_neg, m.zero, map_one]
  change mult m k = -1
  linear_combination he

@[simp] theorem mult_neg (k : Fin q) : mult m (-k) = (mult m k)⁻¹ := m.fieldPower_neg k

@[simp] theorem X_snd (k : Fin q) (w : ZMod p) : (X m k w).2 = k := rfl
@[simp] theorem field_X (k : Fin q) (w : ZMod p) : ZMod.finEquiv p (X m k w).1 = pi m k w :=
  RingEquiv.apply_symm_apply _ _

omit [Fact p.Prime] in
theorem compose_snd (s t : Frame p q) : (compose m.power s t).2 = s.2 + t.2 := rfl

@[simp] theorem field_compose (s t : Frame p q) :
    ZMod.finEquiv p (compose m.power s t).1 =
      ZMod.finEquiv p s.1 + mult m s.2 * ZMod.finEquiv p t.1 := by
  simp [compose, mult, Multipliers.fieldPower]

theorem X_eq_X_iff {k l : Fin q} {w t : ZMod p} :
    X m k w = X m l t ↔ k = l ∧ w = t := by
  constructor
  · intro he
    obtain rfl : k = l := congrArg Prod.snd he
    have eq := congrArg (fun s : Frame p q => ZMod.finEquiv p s.1) he
    simp only [field_X, pi, add_right_inj] at eq
    exact ⟨rfl, mul_left_cancel₀ (one_add_mult_ne_zero m k) eq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

omit [Fact p.Prime] [NeZero q] in
theorem frame_ext {s t : Frame p q} (h : ZMod.finEquiv p s.1 = ZMod.finEquiv p t.1)
    (e : s.2 = t.2) : s = t := Prod.ext ((ZMod.finEquiv p).injective h) e

omit [Fact p.Prime] in
theorem field_power (k : Fin q) : ZMod.finEquiv p (m.power k) = mult m k := rfl

theorem existsUnique_X (s : Frame p q) : ∃! w, X m s.2 w = s := by
  refine ⟨(ZMod.finEquiv p s.1 - (1 - mult m s.2) / 2) / (1 + mult m s.2), ?_, ?_⟩
  · refine frame_ext ?_ rfl
    rw [field_X, pi, mul_div_cancel₀ _ (one_add_mult_ne_zero m s.2)]
    ring
  · intro t ht
    rw [← ht]
    simp only [X_snd, field_X, pi, add_sub_cancel_left,
      mul_div_cancel_left₀ _ (one_add_mult_ne_zero m _)]

variable (h2 : (2 : ZMod p) ≠ 0)
include h2

theorem inverse_X (k : Fin q) (w : ZMod p) : inv m (X m k w) = X m (-k) (-w) := by
  refine frame_ext ?_ rfl
  simp only [inv, map_neg, map_mul, field_X, X_snd, field_power, pi, mult_neg]
  field_simp [mult_ne_zero, h2]
  ring

theorem v_neg (k : Fin q) : v m (-k) = -v m k := by
  unfold v
  rw [mult_neg]
  have ha := mult_ne_zero m k
  have hb := one_add_mult_ne_zero m k
  have hc : mult m k + 1 ≠ 0 := by rwa [add_comm]
  field_simp [h2, ha, hb, hc]
  ring

theorem v_injective : Function.Injective (v m) := by
  intro k l he
  apply mult_injective m
  unfold v at he
  field_simp [h2, one_add_mult_ne_zero] at he
  apply mul_left_cancel₀ h2
  linear_combination -he

omit h2 in
theorem v_zero : v m 0 = 0 := by simp [v]

theorem separated_X_iff (k : Fin q) (w : ZMod p) :
    separated m.power (X m k w) = true ↔
      w ≠ 1 / 2 ∧ w ≠ -(1 / 2) ∧ w ≠ v m k ∧ w ≠ -v m k := by
  have hn := one_add_mult_ne_zero m k
  have pi_neg : pi m k (-v m k) = 0 := by unfold pi v; field_simp [h2, hn] ; ring
  have pi_pos : pi m k (v m k) = 1 - mult m k := by unfold pi v; field_simp [h2, hn] ; ring
  have pi_half : pi m k (1 / 2) = 1 := by unfold pi; field_simp [h2] ; ring
  have pi_nhalf : pi m k (-(1 / 2)) = -mult m k := by unfold pi; field_simp [h2] ; ring
  have inj : Function.Injective (pi m k) := by
    intro a b eq
    exact mul_left_cancel₀ hn (add_left_cancel eq)
  have emb (a b : Fin p) : a ≠ b ↔ ZMod.finEquiv p a ≠ ZMod.finEquiv p b :=
    (ZMod.finEquiv p).injective.ne_iff.symm
  simp only [separated, Bool.and_eq_true, bne_iff_ne, emb, map_zero, map_one, map_add, field_X,
    X_snd, field_power]
  have e₁ : pi m k w = 0 ↔ w = -v m k := by rw [← pi_neg, inj.eq_iff]
  have e₂ : pi m k w = 1 ↔ w = 1 / 2 := by
    exact (iff_of_eq (congrArg (pi m k w = ·) pi_half.symm)).trans inj.eq_iff
  have e₃ : pi m k w + mult m k = 0 ↔ w = -(1 / 2) := by
    rw [add_eq_zero_iff_eq_neg, ← pi_nhalf, inj.eq_iff]
  have e₄ : pi m k w + mult m k = 1 ↔ w = v m k := by
    rw [← eq_sub_iff_add_eq, ← pi_pos, inj.eq_iff]
  tauto


/-- The field-coordinate identity common to both kinds of transition row. -/
theorem sandwich_X (k l : Fin q) (w y : ZMod p) :
    compose m.power (compose m.power (X m k w) (X m l y)) (inv m (X m k (-w))) =
      X m l ((1 + mult m k) * w + mult m k * y) := by
  rw [inverse_X m h2, neg_neg]
  apply frame_ext
  · simp only [field_compose, field_X, X_snd, compose_snd, mult_add, pi, mult_neg]
    field_simp [h2, mult_ne_zero]
    ring
  · change k + l + -k = l
    abel

/-- Lemma 4.4, including either orientation of the target exponent pair. -/
theorem canonical_closure (k l : Fin q) (w : ZMod p) :
    compose m.power (compose m.power (X m k w) (X m l (-w))) (inv m (X m k (-w))) =
      X m l w := by
  rw [sandwich_X m h2]
  congr 1
  ring

/-- Lemma 4.10, for ordinary and exceptional choices of the joining coordinates. -/
theorem transition_closure_iff {K : Fin q} (hK : mult m K = -1 / 2)
    (N : Fin q) (w y z : ZMod p) :
    compose m.power (compose m.power (X m K w) (X m N y)) (inv m (X m K (-w))) =
      X m N z ↔ y = w - 2 * z := by
  rw [sandwich_X m h2, X_eq_X_iff, and_iff_right rfl, hK]
  field_simp [h2]
  constructor <;> intro he <;> linear_combination -he

/-- Zero-coordinate frames form an additive copy of the exponent group. -/
theorem zero_mul (k l : Fin q) :
    compose m.power (X m k 0) (X m l 0) = X m (k + l) 0 := by
  refine frame_ext ?_ rfl
  simp only [field_compose, field_X, X_snd, pi, mult_add]
  field_simp [h2]
  ring

/-- Lemma 5.4, the field identity used to attach the zero-coordinate chain. -/
theorem attachment_mul (a b : Fin q) (hAB : mult m a + mult m b = -2) :
    compose m.power (X m (-a) (-1)) (X m b (-1)) = X m (b - a) 0 := by
  apply frame_ext
  · simp only [field_compose, field_X, X_snd, pi, sub_eq_add_neg, mult_add, mult_neg]
    field_simp [h2, mult_ne_zero]
    linear_combination -2 * hAB
  · change -a + b = b - a
    abel

omit h2 in
theorem translation_X (c : ZMod p) (k : Fin q) (w : ZMod p) :
    compose m.power (T (q := q) c) (X m k w) = X m k (w + c / (1 + mult m k)) := by
  apply frame_ext
  · simp [field_compose, T, pi, mul_add, mul_div_cancel₀ _ (one_add_mult_ne_zero m k)]
    ring
  · change 0 + k = k
    simp


/-- Direct two-product form of the row equation used by `Family.Complete`. -/
theorem row_closed_iff (k l : Fin q) (w y z : ZMod p) :
    compose m.power (X m k w) (X m l y) = compose m.power (X m l z) (X m k (-w)) ↔
      z = (1 + mult m k) * w + mult m k * y := by
  have hn := one_add_mult_ne_zero m l
  constructor
  · intro eq
    have he := congrArg (fun s : Frame p q => ZMod.finEquiv p s.1) eq
    simp only [field_compose, field_X, X_snd, pi] at he
    field_simp [h2] at he
    apply mul_left_cancel₀ hn
    apply mul_left_cancel₀ h2
    linear_combination -he
  · rintro rfl
    apply frame_ext
    · simp only [field_compose, field_X, X_snd, pi]
      field_simp [h2]
      ring
    · exact add_comm k l

theorem canonical_row (k l : Fin q) (w : ZMod p) :
    compose m.power (X m k w) (X m l (-w)) = compose m.power (X m l w) (X m k (-w)) := by
  apply (row_closed_iff m h2 k l w (-w) w).2
  ring

theorem transition_row {K : Fin q} (hK : mult m K = -1 / 2) (N : Fin q) (w z : ZMod p) :
    compose m.power (X m K w) (X m N (w - 2 * z)) =
      compose m.power (X m N z) (X m K (-w)) := by
  apply (row_closed_iff m h2 K N w (w - 2 * z) z).2
  rw [hK]
  field_simp [h2]
  ring

/-- Opposite missing coordinates correspond precisely to opposite exponents. -/
theorem same_missing_pair_iff (k l : Fin q) :
    (v m k = v m l ∨ v m k = -v m l) ↔ k = l ∨ k = -l := by
  rw [← v_neg m h2, (v_injective m h2).eq_iff, (v_injective m h2).eq_iff]

theorem v_ne_half (k : Fin q) : v m k ≠ 1 / 2 := by
  intro he
  unfold v at he
  field_simp [h2, one_add_mult_ne_zero] at he
  apply mult_ne_zero m k
  apply mul_left_cancel₀ h2
  linear_combination -he

theorem v_ne_neg_half (k : Fin q) : v m k ≠ -(1 / 2) := by
  intro he
  exact v_ne_half m h2 (-k) (by rw [v_neg m h2, he, neg_neg])

theorem v_ne_zero {k : Fin q} (hk : k ≠ 0) : v m k ≠ 0 := by
  rw [← v_zero m]
  exact (v_injective m h2).ne hk

omit [NeZero p] in
theorem neg_ne_self_of_ne_zero {w : ZMod p} (hw : w ≠ 0) : -w ≠ w := by
  intro he
  apply hw
  apply mul_left_cancel₀ h2
  linear_combination -he

theorem excluded_nodup {k : Fin q} (hk : k ≠ 0) :
    ([1 / 2, -(1 / 2), v m k, -v m k] : List (ZMod p)).Nodup := by
  have H := v_ne_half m h2 k
  have J := v_ne_neg_half m h2 k
  have V := neg_ne_self_of_ne_zero h2 (v_ne_zero m h2 hk)
  have W := neg_ne_self_of_ne_zero h2 (one_div_ne_zero h2)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil]
  grind

/-- At an ordinary fiber all four sign choices have the same membership. -/
theorem present_signs (k : Fin q) (w : ZMod p) :
    (separated m.power (X m (-k) w) = separated m.power (X m k w)) ∧
    (separated m.power (X m k (-w)) = separated m.power (X m k w)) := by
  constructor <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [separated_X_iff m h2, v_neg m h2, neg_neg] <;> grind

end BipartiteKneser.Coordinates
