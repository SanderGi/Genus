module

public import KneserConstruction.FamilyFiberRows

/-! # Matching the ordinary fiber endpoints with the joining rows -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Family

open Coordinates FiberJoins

private theorem sum_at {α β : Type*} [Fintype α] [AddCommMonoid β]
    (P : α → Prop) [DecidablePred P] (e : α) (uniq : ∀ i, P i ↔ i = e) (f g : α → β) :
    (∑ i, if P i then f i else g i) = (∑ i : {i // ¬P i}, g i.val) + f e := by
  classical
  let v (i : α) := if P i then f i else g i
  let bad := {i : α // ¬¬P i}
  let t : bad := ⟨e, by simpa using (uniq e).2 rfl⟩
  let : Subsingleton bad := ⟨fun a b => Subtype.ext
    (((uniq _).mp (not_not.mp a.property)).trans ((uniq _).mp (not_not.mp b.property)).symm)⟩
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => ¬P i) v
  change _ + (∑ i : bad, v i.val) = _ at hs
  rw [Fintype.sum_subsingleton _ t] at hs
  have left (i : {i // ¬P i}) : v i.val = g i.val := ite_eq_right i.property
  simp only [left] at hs
  simpa only [v, t, (uniq e).2 rfl, ite_true] using hs.symm

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- Combining the joining domains with the exceptional E domain fills all final blocks. -/
theorem last_blocks (m : Multipliers p q) (K N E : Fin q) (c : Case) (hq : 3 ≤ q) :
    (∑ i : Fin (q - 1), quartet m (lastExp K E i) (coord i)) =
      (∑ j, (Joins.row m K N c j).domBag (inverse m)) +
        quartet m E ((q - 1 : ℕ) : ZMod p) := by
  let P (i : Fin (q - 1)) := i.val + 1 = q - 1
  let e : Fin (q - 1) := ⟨q - 2, by omega⟩
  have uniq (i : Fin (q - 1)) : P i ↔ i = e := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [P] at h
      dsimp [e]
      omega
    · rintro rfl
      dsimp [P,e]
      omega
  let drop : Fin (q - 2) ≃ {i : Fin (q - 1) // ¬P i} :=
    { toFun := fun j => ⟨⟨j.val, by have := j.isLt; omega⟩, by
        have := j.isLt
        dsimp [P]
        omega⟩
      invFun := fun i => ⟨i.val.val, by
        have h := i.property
        have := i.val.isLt
        dsimp [P] at h
        omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have eq := sum_at P e uniq (fun i => quartet m E (coord i)) (fun i => quartet m K (coord i))
  have hv (i : Fin (q - 1)) : quartet m (lastExp K E i) (coord i) =
      if P i then quartet m E (coord i) else quartet m K (coord i) := by
    by_cases h : P i <;> simp_all [lastExp, P]
  simp only [hv]
  rw [eq, ← drop.sum_comp]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [drop, Joins.row, Joins.number, coord, quartet, Quad.domBag]
  · congr 1
    change ((q - 2 + 1 : ℕ) : ZMod p) = _
    congr 1
    omega

/-- Combining the signed N outputs with E at the missing fiber fills all first blocks. -/
theorem first_blocks (m : Multipliers p q) (K N E : Fin q) (c : Case) (hq : 3 ≤ q)
    (size : InRange c q) :
    (∑ i : Fin (q - 1), quartet m (firstExp c N E i) (coord i)) =
      (∑ j, (Joins.row m K N c j).ranBag (inverse m)) +
        quartet m E (missing c q : ℤ) := by
  let P (i : Fin (q - 1)) := (i.val : ℤ) + 1 = missing c q
  have bounds : 1 ≤ missing c q ∧ missing c q < q := by cases c <;> simp [missing] <;> omega
  let e : Fin (q - 1) := ⟨(missing c q).toNat - 1, by omega⟩
  have he : (e.val : ℤ) + 1 = missing c q := by dsimp [e]; omega
  have uniq (i : Fin (q - 1)) : P i ↔ i = e := by
    constructor
    · intro h
      apply Fin.ext
      change (i.val : ℤ) + 1 = missing c q at h
      omega
    · rintro rfl
      exact he
  have eq := sum_at P e uniq (fun i => quartet m E (coord i)) (fun i => quartet m N (coord i))
  have hv (i : Fin (q - 1)) : quartet m (firstExp c N E i) (coord i) =
      if P i then quartet m E (coord i) else quartet m N (coord i) := by
    by_cases h : P i <;> simp_all [firstExp, P]
  simp only [hv]
  rw [eq, Joins.ranges m K N c size]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [quartet, coord]
  · change quartet m E ((e.val + 1 : ℕ) : ZMod p) = _
    congr 1
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) he

end BipartiteKneser.Family
