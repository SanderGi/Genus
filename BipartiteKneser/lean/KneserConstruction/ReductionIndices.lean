module

public import KneserConstruction.BoundaryCoordinates
public import KneserConstruction.OrbitInterval
public import Mathlib.Data.Nat.Bits

/-! # The interval and its complement in the positive coordinate range -/

@[expose] public section

namespace BipartiteKneser.Reduction

open Boundary Orbit

/-- The interval starts after the short initial segment of the complement. -/
def start (c : Case) := leftCount c + 1

/-- Number of positive coordinates retained only through the interval transfer. -/
def length (c : Case) (q : ℕ) := q - 1 - count c

/-- First coordinate in the upper segment of the complement. -/
def stop (c : Case) (q : ℕ) := start c + length c q

/-- Positive coordinate of the i-th fiber outside the ordinary interval. -/
def outsideNat (c : Case) (q i : ℕ) :=
  if i < leftCount c then i + 1 else q - (count c - i)

theorem sizes (c : Case) : 0 < leftCount c ∧ leftCount c < count c ∧ count c ≤ 14 := by
  cases c <;> decide

theorem stop_eq (c : Case) {q : ℕ} (hq : 65 ≤ q) : stop c q = q - (count c - leftCount c) := by
  have := sizes c
  unfold stop start length
  omega

theorem outside_cast (c : Case) {q : ℕ} (hq : 65 ≤ q) (i : ℕ) :
    (outsideNat c q i : ℤ) = outside c q i := by
  have := sizes c
  unfold outsideNat outside
  split <;> simp [Nat.cast_sub (show count c - i ≤ q by omega)]

theorem outside_bounds (c : Case) {q i : ℕ} (hq : 65 ≤ q) (hi : i < count c) :
    1 ≤ outsideNat c q i ∧ outsideNat c q i < q ∧ (outsideNat c q i = 1 ↔ i = 0) := by
  have := sizes c
  unfold outsideNat
  split <;> omega

/-- Combine the independent boundary and interval choices into one switch per fiber. -/
def switches (c : Case) (q mask : ℕ) (s : ℕ → Bool) (w : ℕ) : Bool :=
  if w < start c then mask.testBit (w - 1)
  else if w < stop c q then s (w - start c)
  else mask.testBit (w - stop c q + leftCount c)

theorem switches_outside (c : Case) {q i : ℕ} (hq : 65 ≤ q) (hi : i < count c)
    (mask : ℕ) (s : ℕ → Bool) :
    switches c q mask s (outsideNat c q i) = mask.testBit i := by
  have := sizes c
  unfold switches outsideNat
  rw [stop_eq c hq]
  unfold start
  split <;> split_ifs <;> first | omega | exact congrArg mask.testBit (by omega)

theorem switches_inside (c : Case) (q mask : ℕ) (s : ℕ → Bool) {k : ℕ}
    (hk : k < length c q) :
    switches c q mask s (start c + k) = s k := by simp [switches, stop, hk]

/-- Pack the first n values of a Boolean function into the low bits of a numeral. -/
def pack (f : ℕ → Bool) : (n : ℕ) → Fin (2 ^ n)
  | 0 => 0
  | n + 1 => ⟨Nat.bit (f 0) (pack (fun k => f (k + 1)) n).val,
      Nat.bit_lt_two_pow_succ_iff.mpr (Fin.isLt _)⟩

private theorem pack_bit (f : ℕ → Bool) {i n : ℕ} (hi : i < n) :
    (pack f n).val.testBit i = f i := by
  induction n generalizing i f with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero ..
    | succ i => exact (Nat.testBit_bit_succ ..).trans (ih _ (by omega))

/-- Pack the missing-pair indicators at the outside fibers into the boundary mask. -/
def pattern (c : Case) (q : ℕ) (χ : ℕ → Bool) : Pattern c :=
  pack (fun i => χ (outsideNat c q i)) (count c)

theorem pattern_bit (c : Case) (q : ℕ) (χ : ℕ → Bool) {i : ℕ} (hi : i < count c) :
    (pattern c q χ).val.testBit i = χ (outsideNat c q i) := pack_bit _ hi

private theorem word_count (f : ℕ → Bool) (n : ℕ) :
    (wordAt f n).count true = ((List.range n).map f).count true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wordAt, List.range_succ, ih, List.count_cons]

private theorem count_split (χ : ℕ → Bool) (w a b : ℕ) :
    ((List.range' w (a + b)).map χ).count true =
      ((List.range' w a).map χ).count true + ((List.range' (w + a) b).map χ).count true := by
  rw [← List.range'_append_1, List.map_append, List.count_append]

/-- The boundary bit vector and the reversed interval word partition the actual
character count. This allows Lemma 7.1 to use the missing-pair inventory directly. -/
theorem partition_count (c : Case) {q : ℕ} (hq : 65 ≤ q) (χ : ℕ → Bool) :
    (wordAt (fun k => χ (start c + k)) (length c q)).count true +
      ((List.range (count c)).map (pattern c q χ).val.testBit).count true =
    ((List.range' 1 (q - 1)).map χ).count true := by
  have sz := sizes c
  let l := leftCount c
  let r := count c - l
  let n := length c q
  have hc : count c = l + r := by dsimp [l, r]; omega
  have hq' : q - 1 = l + n + r := by dsimp [n, l, r, length]; omega
  have he : (List.range (count c)).map (pattern c q χ).val.testBit =
      (List.range' 1 l).map χ ++ (List.range' (stop c q) r).map χ := by
    calc
      _ = (List.range (count c)).map (fun i => χ (outsideNat c q i)) :=
        List.map_congr_left (fun _ hi => pattern_bit c q χ (List.mem_range.mp hi))
      _ = _ := by
        rw [hc, List.range_add, List.map_append, List.map_map,
          List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
        congr 1
        · apply List.map_congr_left
          intro i hi
          have h := List.mem_range.mp hi
          simp [outsideNat, show i < leftCount c from h, Nat.add_comm]
        · apply List.map_congr_left
          intro i hi
          have h := List.mem_range.mp hi
          simp only [Function.comp_apply, outsideNat,
            show ¬l + i < leftCount c by dsimp [l]; omega,
            ite_false, stop_eq c hq]
          congr 1
          dsimp [l, r] at *
          omega
  rw [he, List.count_append, word_count]
  have inside : (List.range n).map (fun k => χ (start c + k)) =
      (List.range' (start c) n).map χ := by
    rw [List.range'_eq_map_range, List.map_map]; rfl
  rw [inside, hq', count_split, count_split]
  simp only [stop, start, l, n, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end BipartiteKneser.Reduction
