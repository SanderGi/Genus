module

public import KneserConstruction.Multipliers
public import Mathlib.Data.Finset.Powerset

/-! # The cardinality of the connection set -/

@[expose] public section

namespace BipartiteKneser.Criterion

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- Use the frame chart to count the two-element subsets avoiding both base points. -/
theorem card_label (m : Multipliers p q) (hp : 2 ≤ p) :
    Fintype.card {s : Frame p q // separated m.power s = true} = (p - 2) * (p - 3) / 2 := by
  classical
  let c : BaseCycle p q 1 := ⟨m.power, fun _ => (0, 0), fun _ => 0⟩
  let ch := m.chart c rfl
  let pts (s : Frame p q) : Finset (Fin p) := {(c.sortedPoints s).1, (c.sortedPoints s).2}
  let available := ((Finset.univ : Finset (Fin p)).erase 0).erase 1
  have valid (s : Frame p q) : pts s ⊆ available ↔ separated m.power s = true := by
    simp only [pts, available, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_erase, Finset.mem_univ, and_true, separated, Bool.and_eq_true, bne_iff_ne,
      BaseCycle.sortedPoints, BaseCycle.points, c]
    by_cases h : s.1 < s.1 + m.power s.2 <;> simp [h] <;> tauto
  have count (s : Frame p q) : (pts s).card = 2 :=
    Finset.card_pair (ne_of_lt (ch.increasing s))
  let f (s : {s : Frame p q // separated m.power s = true}) :
      ↥(available.powersetCard 2) :=
    ⟨pts s, Finset.mem_powersetCard.mpr ⟨(valid s).mpr s.property, count s⟩⟩
  have bij : Function.Bijective f := by
    constructor
    · intro x y he
      have sets : pts x = pts y := congrArg Subtype.val he
      have mem₁ : (c.sortedPoints x).1 ∈ pts y := sets ▸ Finset.mem_insert_self _ _
      have mem₂ : (c.sortedPoints x).2 ∈ pts y := sets ▸ Finset.mem_insert_of_mem (by simp)
      have hx := ch.increasing x
      have hy := ch.increasing y
      simp only [pts, Finset.mem_insert, Finset.mem_singleton] at mem₁ mem₂
      have hpairs : c.sortedPoints x = c.sortedPoints y := Prod.ext (by grind) (by grind)
      exact Subtype.ext ((ch.leftInv x).symm.trans (hpairs ▸ ch.leftInv y))
    · rintro ⟨t, ht⟩
      obtain ⟨sub, ht⟩ := Finset.mem_powersetCard.mp ht
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht
      have realize (a b : Fin p) (hab : a < b) : pts (ch.decode a b) = {a, b} := by
        simp [pts, ch.rightInv a b hab]
      have ex : ∃ s, pts s = {a, b} := by
        rcases lt_or_gt_of_ne hab with h | h
        · exact ⟨_, realize _ _ h⟩
        · exact ⟨_, (realize _ _ h).trans (Finset.pair_comm ..)⟩
      obtain ⟨s, hs⟩ := ex
      exact ⟨⟨s, (valid s).mp (hs ▸ sub)⟩, Subtype.ext hs⟩
  have oneNe : (1 : Fin p) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt hp] at this
  rw [Fintype.card_congr (Equiv.ofBijective f bij), Fintype.card_coe, Finset.card_powersetCard,
    Nat.choose_two_right]
  have ha : available.card = p - 2 := by
    simp [available, Finset.card_erase_of_mem, oneNe, Nat.sub_sub]
  rw [ha, Nat.sub_sub]

end BipartiteKneser.Criterion
