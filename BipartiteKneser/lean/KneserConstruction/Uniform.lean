module

public import KneserConstruction.PaperOrder
public import KneserConstruction.InventoryBlocks
public import KneserConstruction.FamilyConstruction

/-! # Existence of the input to the generic rotation construction -/

@[expose] public section

namespace BipartiteKneser.Family

open Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Choose the three distinguished pairs, the two attachment exponents, and the
complete ordered lists at every positive fiber. -/
theorem exists_construction (m : Multipliers p q) {M : ℕ}
    (large : 16 ≤ M) (hp : p = 8 * M + 3) (hq : q = 4 * M + 1) :
    ∃ C : Construction m, C.M = M ∧ C.CoversOrders ∧ ∀ i : Fin (q - 1),
      (C.middle i).length % 2 == 0 ↔ missingBit p (i.val + 1) = false := by
  classical
  have size : p = 2 * q + 1 := by omega
  have qsize : q = 2 * (2 * M) + 1 := by omega
  have big : 131 ≤ p := by omega
  have res : p % 8 = 3 := by omega
  obtain ⟨d⟩ := special_exists m (by omega) res
  obtain ⟨P⟩ := Parameters.exists_exponents m d.K d.N d.E size big res
  choose mid hcover hlength using
    FiberOrder.exists_middle d P size qsize big res
  let C : Construction m := ⟨M, large, hp, hq, d, P, mid⟩
  refine ⟨C, rfl, ?_, ?_⟩
  · unfold Construction.CoversOrders
    rw [Inventory.partition m C.two_ne size qsize, Inventory.translation_blocks m size qsize,
      Inventory.zero_blocks m (M := M) rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Construction.order, Construction.first, Construction.last,
      Construction.residueCase, FiberOrder.paperCase, C, coord, Nat.cast_add, Nat.cast_one] using
      (hcover i).symm
  · intro i
    have len := hlength i
    change (mid i).length % 2 == 0 ↔ _
    by_cases zero : i.val = 0 <;> cases h : missingBit p (i.val + 1) <;>
      simp only [h, Bool.toNat_false, Bool.toNat_true] at len <;>
      simp [fiberOrder, zero] at len <;> simp <;> omega

end BipartiteKneser.Family
