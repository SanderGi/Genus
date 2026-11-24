import KneserConstruction.Coordinates

/-!
# Signed representatives for the coordinate and exponent fibers
-/

namespace BipartiteKneser.Coordinates

variable {n t : ℕ} [NeZero n]

private def signedIndex (size : n = 2 * t + 1) (i : Fin t × Bool) :
    {x : Fin n // x ≠ 0} :=
  let a : Fin n := ⟨i.1.val + 1, by have := i.1.isLt; omega⟩
  have ha : a ≠ 0 := Fin.val_ne_zero_iff.mp (Nat.succ_ne_zero _)
  if i.2 then ⟨-a, neg_ne_zero.mpr ha⟩ else ⟨a, ha⟩

private theorem signedIndex_val (size : n = 2 * t + 1) (i : Fin t) (s : Bool) :
    (signedIndex size (i,s)).val.val = if s then n - (i.val + 1) else i.val + 1 := by
  cases s
  · rfl
  · simp [signedIndex, Fin.val_neg, ← Fin.val_eq_zero_iff]

/-- The nonzero residues of an odd modulus are the signed positive half-range.
The Boolean is false on the positive half. -/
noncomputable def signedResidueEquiv (size : n = 2 * t + 1) :
    (Fin t × Bool) ≃ {x : Fin n // x ≠ 0} := by
  apply Equiv.ofBijective (signedIndex size)
  constructor
  · rintro ⟨i, s⟩ ⟨j, b⟩ he
    have h := congrArg (fun x : {x : Fin n // x ≠ 0} => x.val.val) he
    simp only [signedIndex_val] at h
    have hi := i.isLt
    have hj := j.isLt
    cases s <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
    · have hi' : i.val = j.val := by omega
      rw [Fin.ext hi']
    · omega
    · omega
    · have hi' : i.val = j.val := by omega
      rw [Fin.ext hi']
  · rintro ⟨x, hx⟩
    have hn := Fin.val_ne_zero_iff.mpr hx
    have hxlt := x.isLt
    by_cases hl : x.val ≤ t
    · refine ⟨(⟨x.val - 1, by omega⟩, false), Subtype.ext (Fin.ext ?_)⟩
      rw [signedIndex_val]
      simp
      omega
    · refine ⟨(⟨n - x.val - 1, by omega⟩, true), Subtype.ext (Fin.ext ?_)⟩
      rw [signedIndex_val]
      simp
      omega

@[simp] theorem signedResidueEquiv_pos (size : n = 2 * t + 1) (i : Fin t) :
    (signedResidueEquiv size (i, false)).val = (Fin.ofNat n (i.val + 1)) := by
  apply Fin.ext
  change (signedIndex size (i,false)).val.val = _
  rw [signedIndex_val, Fin.val_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  rfl

@[simp] theorem signedResidueEquiv_neg (size : n = 2 * t + 1) (i : Fin t) :
    (signedResidueEquiv size (i, true)).val = -(Fin.ofNat n (i.val + 1)) := by
  change -((signedResidueEquiv size (i, false)).val) = _
  rw [signedResidueEquiv_pos]

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

omit [NeZero p] [NeZero q] in
theorem top_fiber (h2 : (2 : ZMod p) ≠ 0) (size : p = 2 * q + 1) :
    (q : ZMod p) = -(1 / 2) := by
  -- Keep the field modulus fixed when casting the natural size equation.
  have eq : (p : ZMod p) = 2 * (q : ZMod p) + 1 := by
    simpa using congrArg (Nat.cast : ℕ → ZMod p) size
  rw [ZMod.natCast_self] at eq
  field_simp [h2]
  linear_combination -eq

theorem separated_T_iff (m : Multipliers p q) (c : ZMod p) :
    separated m.power (T (q := q) c) = true ↔ c ≠ 0 ∧ c ≠ 1 ∧ c ≠ -1 := by
  have emb (a b : Fin p) : a ≠ b ↔ ZMod.finEquiv p a ≠ ZMod.finEquiv p b :=
    (ZMod.finEquiv p).injective.ne_iff.symm
  simp only [separated, T, m.zero, Bool.and_eq_true, bne_iff_ne, emb,
    RingEquiv.apply_symm_apply, map_add, map_one, map_zero]
  grind

end BipartiteKneser.Coordinates
