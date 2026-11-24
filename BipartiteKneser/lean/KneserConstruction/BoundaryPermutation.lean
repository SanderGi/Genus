import KneserConstruction.BoundaryModel
import Mathlib.Data.Fintype.EquivFin

/-! Every choice of the local bijections gives a permutation (Proposition 7.2). -/

namespace BipartiteKneser.Boundary

/-- Route a last-pair slot or an exit port to its numbered boundary label. -/
private def routing (c : Case) (x : Label c) : Label c := Fin.ofNat _ <|
  if x.val < 4 * count c then routeIndex c (x.val / 4) (x.val % 4)
  else exitIndex c (x.val - 4 * count c)

private theorem routing_injective (c : Case) : Function.Injective (routing c) := by
  unfold Function.Injective
  cases c <;> decide +kernel

/-- The chosen bijection lands in one of the four slots of the last exponent pair. -/
theorem lastSlot_lt (i x : Nat) (b s : Bool) : lastSlot i x b s < 4 := by
  exact (show ∀ a d : Bool, 2 * a.toNat + d.toNat < 4 from by decide) _ _

private theorem slot_inj (i : Nat) (b s : Bool) (j k : Fin 4)
    (eq : lastSlot i j b s = lastSlot i k b s) : j = k := by
  have h : ∀ (z : Fin 2) (m a : Bool) (u v : Fin 4),
      lastSlot z u m a = lastSlot z v m a → u = v := by decide
  by_cases hi : i = 0
  · subst i
    exact h 0 b s j k eq
  · apply h 1 b s j k
    change lastSlot 1 j b s = lastSlot 1 k b s
    simpa only [lastSlot, hi, Nat.one_ne_zero, ↓reduceIte] using eq

/-- A forward transfer lands on one of the six exit ports. -/
theorem transferIndex_lt (p r : Interval.Perm) (x : Nat) : transferIndex p r x < 6 := by
  unfold transferIndex
  generalize Interval.image _ _ = v
  have := v.isLt
  split <;> omega

private theorem transfer_inj : ∀ (p r : Interval.Perm) (x y : Fin 6),
    transferIndex p r x = transferIndex p r y → x = y := by decide +kernel

/-- The local choice permutes each four-element fiber and each three-element entry strand. -/
private def rearrange (c : Case) (chars : Pattern c) (mask : Nat) (p r : Interval.Perm)
    (x : Label c) : Label c :=
  if h : x.val < 4 * count c then
    let i := x.val / 4
    let j := lastSlot i (x.val % 4) (chars.val.testBit i) (mask.testBit i)
    ⟨4 * i + j, by
      have hj : j < 4 := lastSlot_lt ..
      dsimp [size, i]
      omega⟩
  else ⟨4 * count c + transferIndex p r (x.val - 4 * count c), by
    have ht := transferIndex_lt p r (x.val - 4 * count c)
    unfold size
    omega⟩

private theorem rearrange_injective (c : Case) (chars : Pattern c) (mask : Nat)
    (p r : Interval.Perm) : Function.Injective (rearrange c chars mask p r) := by
  intro x y h
  have eq := congrArg Fin.val h
  dsimp only [rearrange] at eq
  have hx := x.isLt
  have hy := y.isLt
  unfold size at hx hy
  split at eq <;> split at eq <;> dsimp only at eq
  · rename_i hx' hy'
    have bx := lastSlot_lt (x.val / 4) (x.val % 4)
      (chars.val.testBit (x.val / 4)) (mask.testBit (x.val / 4))
    have by' := lastSlot_lt (y.val / 4) (y.val % 4)
      (chars.val.testBit (y.val / 4)) (mask.testBit (y.val / 4))
    have hi : x.val / 4 = y.val / 4 := by omega
    rw [hi] at eq
    have hj := slot_inj (y.val / 4) (chars.val.testBit _) (mask.testBit _)
      ⟨x.val % 4, by omega⟩ ⟨y.val % 4, by omega⟩ (Nat.add_left_cancel eq)
    exact Fin.ext (by
      have := congrArg Fin.val hj
      dsimp at this
      omega)
  · have bx := lastSlot_lt (x.val / 4) (x.val % 4)
      (chars.val.testBit (x.val / 4)) (mask.testBit (x.val / 4))
    omega
  · have by' := lastSlot_lt (y.val / 4) (y.val % 4)
      (chars.val.testBit (y.val / 4)) (mask.testBit (y.val / 4))
    omega
  · have hj := transfer_inj p r ⟨x.val - 4 * count c, by omega⟩
      ⟨y.val - 4 * count c, by omega⟩ (Nat.add_left_cancel eq)
    exact Fin.ext (by
      have := congrArg Fin.val hj
      dsimp at this
      omega)

private theorem step_factor (c : Case) (chars : Pattern c) (mask : Nat) (p r : Interval.Perm)
    (x : Label c) : step c chars mask p r x = routing c (rearrange c chars mask p r x) := by
  unfold step nextIndex routing rearrange
  split <;> rename_i h
  · have hj := lastSlot_lt (x.val / 4) (x.val % 4)
      (chars.val.testBit (x.val / 4)) (mask.testBit (x.val / 4))
    simp (disch := omega) only [ite_eq_left, Nat.mul_add_div (by decide : 0 < 4),
      Nat.div_eq_of_lt hj, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  · simp

/-- Proposition 7.2. Every choice of outside bijections and forward transfers is bijective. -/
theorem step_bijective (c : Case) (chars : Pattern c) (mask : Nat) (p r : Interval.Perm) :
    Function.Bijective (step c chars mask p r) := by
  have inj : Function.Injective (step c chars mask p r) := by
    intro x y eq
    rw [step_factor, step_factor] at eq
    exact rearrange_injective c chars mask p r (routing_injective c eq)
  exact ⟨inj, Finite.surjective_of_injective inj⟩

end BipartiteKneser.Boundary
