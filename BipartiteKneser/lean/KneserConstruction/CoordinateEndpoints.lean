module

public import KneserConstruction.CoordinateMissing

/-! # Endpoints of the coordinate-fiber chains -/

@[expose] public section

namespace BipartiteKneser.Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- Positive fiber where N is absent. -/
def w₀ (p q : ℕ) : ℕ := if p % 3 = 1 then 1 else q - 2

namespace Special

variable (d : Special m)

/-- Proposition 4.7 in the positive representative convention of the constructor. -/
theorem addresses (size : p = 2 * q + 1) (large : 19 ≤ p) :
    foldCoord (v m d.K) = q - 1 ∧ foldCoord (v m d.N) = w₀ p q := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  obtain ⟨K, N, _⟩ := d.values large
  have q1 : ((q - 1 : ℕ) : ZMod p) = -(3 / 2) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, top_fiber h₂ size]
    field_simp [h₂]
    ring
  have q2 : ((q - 2 : ℕ) : ZMod p) = -(5 / 2) := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat, top_fiber h₂ size]
    field_simp [h₂]
    ring
  constructor
  · rw [K, ← fold_neg, ← q1]
    exact fold_nat size (by omega) (by omega)
  · rw [N, w₀]
    split_ifs
    · simpa using (fold_nat (p := p) size (w := 1) (by omega) (by omega))
    · rw [← fold_neg, ← q2]
      exact fold_nat size (by omega) (by omega)

theorem present_K_iff (size : p = 2 * q + 1) (large : 19 ≤ p) {w : ℕ}
    (pos : 0 < w) (lt : w < q) :
    separated m.power (X m d.K w) = true ↔ w ≠ q - 1 := by
  rw [present_iff_fold m size (natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)) pos lt,
    (d.addresses size large).1]

theorem present_N_iff (size : p = 2 * q + 1) (large : 19 ≤ p) {w : ℕ}
    (pos : 0 < w) (lt : w < q) :
    separated m.power (X m d.N w) = true ↔ w ≠ w₀ p q := by
  rw [present_iff_fold m size (natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)) pos lt,
    (d.addresses size large).2]

/-- The auxiliary endpoint E is available at both exceptional fibers. -/
theorem present_E_endpoints (size : p = 2 * q + 1) (large : 19 ≤ p) :
    separated m.power (X m d.E ((q - 1 : ℕ) : ZMod p)) = true ∧
    separated m.power (X m d.E (w₀ p q)) = true := by
  obtain ⟨_, _, _, _, _, K, K', N, N'⟩ := d.distinct large
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have wpos : 0 < w₀ p q := by unfold w₀; split <;> omega
  have wlt : w₀ p q < q := by unfold w₀; split <;> omega
  obtain ⟨ka, na⟩ := d.addresses size large
  rw [present_iff_fold m size h₂ (by omega) (by omega),
    present_iff_fold m size h₂ wpos wlt, ← ka, ← na]
  constructor <;> intro he
  · exact ((same_missing_pair_iff m h₂ _ _).1 (fold_eq he)).elim K K'
  · exact ((same_missing_pair_iff m h₂ _ _).1 (fold_eq he)).elim N N'

/-- The only possible missing pair at 1 is the N pair in the first residue class.
Thus the attachment exponents supplied by Lemma 5.5 are both present. -/
theorem present_at_one (size : p = 2 * q + 1) (large : 19 ≤ p) (res : p % 8 = 3)
    {k : Fin q} (hn : k ≠ d.N) (hn' : k ≠ -d.N) :
    separated m.power (X m k 1) = true := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by decide) (by omega)
  have classify (j : Fin q) (hj : v m j = 1) : j = d.N := by
    have b : (1 : ZMod p) + 2 * 1 ≠ 0 := by norm_num; exact h₃
    have val := (v_eq_iff_mult m h₂ j 1 b).1 hj
    norm_num at val
    by_cases h : p % 3 = 1
    · apply mult_injective m
      simpa [d.power_N, nValue, h, div_eq_mul_inv] using val
    · have H : mult m d.N = -2 / 3 := by simpa [nValue, h] using d.power_N
      have sq := (m.square d.N).div (m.square j)
      change IsSquare (mult m d.N / mult m j) at sq
      have eq : mult m d.N / mult m j = 2 := by
        apply (div_eq_iff (mult_ne_zero m j)).2
        rw [H, val]
        field_simp [h₃]
      rw [eq, ZMod.exists_sq_eq_two_iff (by omega)] at sq
      omega
  obtain ⟨a,b⟩ := ordinary_ne_half size h₂ (w := 1) (by omega) (by omega)
  rw [separated_X_iff m h₂]
  refine ⟨by simpa using a, by simpa using b, fun h => hn (classify k h.symm), ?_⟩
  intro h
  have eq := classify (-k) (by rw [v_neg m h₂, ← h])
  exact hn' (by rw [← eq, neg_neg])

/-- The chosen first and last exponents are both present and in distinct pairs. -/
theorem chain_endpoints (size : p = 2 * q + 1) (large : 19 ≤ p) {w : ℕ}
    (pos : 0 < w) (lt : w < q) :
    let first := if w = w₀ p q then d.E else d.N
    let last := if w = q - 1 then d.E else d.K
    separated m.power (X m first w) = true ∧ separated m.power (X m last w) = true ∧
      first ≠ last ∧ first ≠ -last := by
  have diff : w₀ p q ≠ q - 1 := by unfold w₀; split <;> omega
  obtain ⟨_, _, _, KN, KN', KE, KE', NE, NE'⟩ := d.distinct large
  obtain ⟨atK, atN⟩ := d.present_E_endpoints size large
  dsimp only
  split_ifs with A B B
  · exact (diff (A.symm.trans B)).elim
  · exact ⟨by simpa [A] using atN, (d.present_K_iff size large pos lt).2 B, Ne.symm KE,
      fun h => KE' (by rw [h, neg_neg])⟩
  · exact ⟨(d.present_N_iff size large pos lt).2 A, by simpa [B] using atK, NE, NE'⟩
  · exact ⟨(d.present_N_iff size large pos lt).2 A, (d.present_K_iff size large pos lt).2 B,
      Ne.symm KN, fun h => KN' (by rw [h, neg_neg])⟩

/-- Field values for the other orientation of each distinguished exponent pair. -/
theorem reciprocal_values (large : 19 ≤ p) :
    mult m (-d.K) = -2 ∧ mult m (-d.N) = (if p % 3 = 1 then -3 else -3 / 2) ∧
      mult m (-d.E) = 1 / 4 := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by decide) (by omega)
  simp only [mult_neg, d.power_K, d.power_N, d.power_E, nValue]
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> field_simp [h₂, h₃]

end Special
end BipartiteKneser.Coordinates
