module

public import KneserConstruction.OrbitRows
public import KneserConstruction.CriterionRows

/-! # Substituting actual affine frames into symbolic splice rows -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Orbit

open Family

variable {p q : ℕ} [NeZero p] [NeZero q] {m : Multipliers p q}

/-- Inverting an affine frame twice recovers the frame. -/
theorem inverse_twice (m : Multipliers p q) (x : Frame p q) :
    inverse m (inverse m x) = x := @inv_inv (Criterion.AffineFrame m) _ x

/-- A block supplies the two positive representatives U,V; its other two
addresses are their inverses. -/
def named (m : Multipliers p q) (pairs : ℕ → Bool → Frame p q) (i : ℕ) : Frame p q :=
  let x := pairs (i / 4) (i.testBit 1)
  if i.testBit 0 then inverse m x else x

/-- The inverse partner of a symbolic address names the inverse affine frame. -/
theorem named_mate (pairs : ℕ → Bool → Frame p q) (i : ℕ) :
    named m pairs (Splice.mate i) = inverse m (named m pairs i) := by
  have hd : (i ^^^ 1) / 4 = i / 4 := by
    change (i ^^^ 1) / 2^2 = _
    rw [Nat.xor_div_two_pow]
    simp
  simp only [named, Splice.mate, hd, Nat.testBit_xor]
  have h0 : (1 : ℕ).testBit 0 = true := by decide
  have h1 : (1 : ℕ).testBit 1 = false := by decide
  rw [h0, h1]
  cases i.testBit 0 <;> simp [inverse_twice]

/-- The four consecutive addresses of a block name its two representatives and their inverses in
pair-block order. -/
theorem named_block (pairs : ℕ → Bool → Frame p q) (b : ℕ) :
    named m pairs ∘ Splice.addr b = pairBlock (m := m) (pairs b false) (pairs b true) := by
  funext i
  have bits (j : ℕ) (hj : j < 2) : (4 * b + i.val).testBit j = i.val.testBit j := by
    have h := Nat.testBit_mod_two_pow (4 * b + i.val) 2 j
    rw [show (4 * b + i.val) % 2^2 = i.val by omega] at h
    simpa [hj] using h.symm
  change named m pairs (4 * b + i.val) = _
  simp only [named, show (4 * b + i.val) / 4 = b by omega, bits 0 (by decide), bits 1 (by decide)]
  fin_cases i <;> rfl

/-- The actual family row named by the four addresses. -/
def instantiate (label : ℕ → Frame p q) (r : Splice.Row) : Quad (Frame p q) :=
  ⟨label r.a, label r.b, label r.c, label r.d⟩

/-- Every source of such a row is represented by a symbolic address. -/
def domAddress (r : Splice.Row) : Slot → ℕ
  | (false, false) => r.a
  | (false, true) => Splice.mate r.a
  | (true, false) => r.b
  | (true, true) => Splice.mate r.b

/-- Looking up a symbolic source address gives the source of the corresponding instantiated
quadruple. -/
theorem named_dom (pairs : ℕ → Bool → Frame p q) (r : Splice.Row) (s : Slot) :
    (instantiate (named m pairs) r).dom (inverse m) s = named m pairs (domAddress r s) := by
  obtain ⟨i, j⟩ := s
  cases i <;> cases j <;> simp [instantiate, domAddress, Quad.dom, named_mate]

end BipartiteKneser.Orbit
