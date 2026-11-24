module

public import KneserConstruction.OrbitRows
public import KneserConstruction.FamilyFiberRows
public import KneserConstruction.ReductionLocal

/-! # Reading the first-to-last fiber map in the boundary convention -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Orbit

open Family Coordinates Boundary Reduction

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q} {ι : Type*}

/-- Boundary slot to pair-block slot. -/
def fromSlot : Fin 4 → Fin 4 := ![0, 2, 3, 1]

/-- Convert a slot in the order U, U⁻¹, V, V⁻¹ to the boundary checker’s order. -/
def toSlot : Fin 4 → Fin 4 := ![0, 3, 1, 2]

/-- Converting a pair-block slot to boundary order and back recovers the slot. -/
theorem slot_inverse : ∀ i, fromSlot (toSlot i) = i := by decide

/-- A signed boundary point and its corresponding fiber slot denote the same affine frame. -/
theorem signed_slot (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ℤ) (i : Fin 4) :
    signedFrame m k (slotPoint w i.val) = fiber m k (w : ZMod p) (fromSlot i) := by
  fin_cases i <;> norm_num [signedFrame, slotPoint, fiber, pairBlock, fromSlot,
    Nat.testBit_eq_decide_div_mod_eq, inverse_X' m h2]

omit [NeZero q] in
private theorem switches_false (k : Fin q) (ls : List (Fin q)) :
    switchTotal (fun _ => false) k ls = false := by
  induction ls generalizing k <;> simp [switchTotal, *]

private theorem chain_source {w : ZMod p} {k : Fin q} {ls : List (Fin q)}
    {s : Fin q → Bool} {Q : Quad (Frame p q)} (h : Q ∈ chain m w s k ls) (slot : Slot) :
    ∃ e ∈ k :: ls, ∃ i, Q.dom (inverse m) slot = fiber m e w i := by
  induction ls generalizing k with
  | nil => simp [chain] at h
  | cons l ls ih =>
    rcases List.mem_cons.mp h with rfl | h
    · refine ⟨k, .head _, ?_⟩
      obtain ⟨a, b⟩ := slot
      cases a <;> cases b
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain ⟨e, he, i, hi⟩ := ih h
      exact ⟨e, .tail _ he, i, hi⟩

private theorem move_last : ∀ (o s : Bool) (i : Fin 4),
    fiberMove true s (fiberMove o false i) = fiberMove (!o) s i := by decide

/-- Compute the slot map to the final exponent pair from the number of intermediate pairs and the
last switch. Every source in the chain reaches that final pair. -/
theorem toLast_paths (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0)
    (w : ZMod p) (s : Bool) (k : Fin q) (mid : List (Fin q)) (l : Fin q)
    (rows : ∀ Q ∈ toLast m w s k mid l, HasRow F Q) :
    Across (onFrames F) (fiber m k w) (fiber m l w) (fiberMove (mid.length % 2 == 0) s) ∧
    ∀ Q ∈ toLast m w s k mid l, ∀ slot, ∃ i,
      Reach (onFrames F) (Q.dom (inverse m) slot) (fiber m l w i) := by
  obtain ⟨chainPath, chainDrain⟩ := chain_paths F h2 w (fun _ => false) k mid
    (fun Q h => rows _ (List.mem_append_left _ h))
  rw [switches_false] at chainPath
  have last := canonical_path F h2 (mid.getLastD k) l w s
    (rows _ (List.mem_append_right _ (.head _)))
  have odd : (mid.length % 2 == 0) = !(mid.length % 2 == 1) := by
    by_cases he : mid.length % 2 = 0 <;> simp_all
  constructor
  · intro i
    rw [odd, ← move_last]
    exact (chainPath i).trans (last _)
  · intro Q h slot
    rcases List.mem_append.mp h with h | h
    · obtain ⟨e, he, i, hi⟩ := chain_source h slot
      obtain ⟨j, hj⟩ := chainDrain e he i
      exact ⟨_, hi ▸ hj.trans (last j)⟩
    · obtain rfl := List.mem_singleton.mp h
      obtain ⟨u, v⟩ := slot
      cases u <;> cases v
      · exact ⟨_, last 0⟩
      · exact ⟨_, last 1⟩
      · exact ⟨_, last 2⟩
      · exact ⟨_, last 3⟩

/-- In the modified fiber the canonical first row precedes the zero-coordinate splice. -/
def startMove (attach : Bool) (i : Fin 4) :=
  if attach then Splice.zeroExit (Splice.first i) else i

/-- Follow a fiber through its canonical rows and, at coordinate one, its zero-coordinate splice.
Every source in a fiber row reaches the last exponent pair. -/
theorem fiberRows_paths (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0)
    (w : ZMod p) (s : Bool) (f l a b : Fin q) (mid : List (Fin q)) (attach : Bool)
    (atOne : attach = true → w = 1)
    (zero : Across (onFrames F) (fiber m a 1) (fiber m b 1) Splice.zeroExit)
    (rows : ∀ Q ∈ fiberRows m w s f l a b mid attach, HasRow F Q) :
    Across (onFrames F) (fiber m f w) (fiber m l w)
      (fiberMove (mid.length % 2 == 0) s ∘ startMove attach) ∧
    ∀ Q ∈ fiberRows m w s f l a b mid attach, ∀ slot, ∃ i,
      Reach (onFrames F) (Q.dom (inverse m) slot) (fiber m l w i) := by
  cases attach
  · exact toLast_paths F h2 w s f mid l rows
  · obtain rfl := atOne rfl
    have head := canonical_path F h2 f a 1 false (rows _ (.head _))
    obtain ⟨tail, drain⟩ := toLast_paths F h2 1 s b mid l (fun Q h => rows _ (.tail _ h))
    have whole (i) := ((head i).trans (zero _)).trans (tail _)
    refine ⟨whole, ?_⟩
    intro Q h slot
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨u, v⟩ := slot
      cases u <;> cases v
      · exact ⟨_, whole 0⟩
      · exact ⟨_, whole 1⟩
      · exact ⟨_, whole 2⟩
      · exact ⟨_, whole 3⟩
    · exact drain _ h slot

private theorem packed_move : ∀ (attach missing s : Bool) (i : Fin 4),
    lastSlot (if attach then 0 else 1) i.val missing s =
      (toSlot (fiberMove (!missing) s (startMove attach (fromSlot i)))).val := by decide

/-- Identify the endpoint of the quadruple chain with the boundary checker slot. -/
theorem packed_last {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) (missing s : Bool) :
    lastSlot (w - 1) i.val missing s =
      (toSlot (fiberMove (!missing) s (startMove (decide (w = 1)) (fromSlot i)))).val := by
  by_cases h : w = 1
  · subst w
    exact packed_move true missing s i
  · simpa [lastSlot, h, show w - 1 ≠ 0 by omega] using packed_move false missing s i

end BipartiteKneser.Orbit
