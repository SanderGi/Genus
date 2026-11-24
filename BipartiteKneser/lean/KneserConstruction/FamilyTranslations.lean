import KneserConstruction.FamilyTransClosure
import KneserConstruction.FamilyTransCoverage
import KneserConstruction.FamilyChains

/-! # Inventories of the closed translation block (Constructions 4.14 and 5.2) -/

namespace BipartiteKneser.Family.Translations

open Coordinates

variable {p q r : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- The full multiset of signed translations. -/
def translationBag (m : Multipliers p q) (r : ℕ) : Multiset (Frame p q) :=
  ∑ i : Fin r, (pair (inverse m) (U i) + pair (inverse m) (V i))

private theorem label_inventory (m : Multipliers p q) (k : Fin q) (w : ZMod p) :
    (∑ x : Row r × Slot, ({label m k w x} : Multiset _)) =
      translationBag m r + quartet m k w := by
  rw [Fintype.sum_prod_type, Fintype.sum_option, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, label, Bool.false_eq_true, ite_false,
      ite_true, pair]
    ac_rfl
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, label, Bool.false_eq_true, ite_false,
      ite_true, quartet, pair]
    ac_rfl

variable (m : Multipliers p q) (L : Layout r) (E : Fin q) (wa wb : ZMod p)

theorem dom_inventory :
    ∑ i, (row m L E wa wb i).domBag (inverse m) = translationBag m r + quartet m E wa := by
  rw [← label_inventory]
  refine Eq.trans ?_ (Equiv.sum_comp (domain L) (fun x => ({label m E wa x} : Multiset _)))
  rw [Fintype.sum_prod_type]
  simp only [domain_val m L E wa wb, Quad.dom_inventory]

theorem ran_inventory (h₂ : (2 : ZMod p) ≠ 0) :
    ∑ i, (row m L E wa wb i).ranBag (inverse m) = translationBag m r + quartet m E wb := by
  rw [← quartet_neg m h₂ E wb, ← label_inventory]
  refine Eq.trans ?_ (Equiv.sum_comp (range L) (fun x => ({label m (-E) wb x} : Multiset _)))
  rw [Fintype.sum_prod_type]
  simp only [range_val m L E wa wb, Quad.ran_inventory]

end BipartiteKneser.Family.Translations
