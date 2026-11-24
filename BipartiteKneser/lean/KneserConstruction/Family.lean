import KneserConstruction.FamilyConstruction

/-!
# The complete admissible family of Proposition 5.7

The positive-fiber indices retain their full exponent orders as a reference
inventory. Joining rows, translation replacements, and zero-coordinate
replacements fill exactly the omitted blocks. Signs of the final transitions
are free at every fiber.
-/

noncomputable section

namespace BipartiteKneser.Family.Construction

open Coordinates FiberJoins

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable {m : Multipliers p q} (C : Construction m)

private theorem sum_get {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map xs f)

private theorem row_sum (switch : ℕ → Bool) (f : Quad (Frame p q) → Multiset (Frame p q)) :
    (∑ i, f (C.row switch i)) =
    (∑ i, ((C.ordinary switch i).map f).sum) +
    ((∑ i, f (C.joins i)) + ((∑ i, f (C.translations i)) + (C.zeros.map f).sum)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [row, sum_get]

include C in
private theorem single_gap (k : Fin q) :
    (∑ i : Fin (q - 1), if decide (i.val = 0) then quartet m k (coord i) else 0) =
      quartet m k 1 := by
  let e : Fin (q - 1) := ⟨0, by have := C.q_eq; have := C.large; omega⟩
  have he (i : Fin (q - 1)) : i.val = 0 ↔ i = e := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [decide_eq_true_eq, he, Fintype.sum_ite_eq', coord, e, Nat.zero_add, Nat.cast_one]

private theorem zero_inventory :
    let total := ∑ i : Fin C.M, Zero.block m (Zero.start i.val)
    (C.zeros.map (Quad.domBag (inverse m))).sum = total + quartet m C.params.a 1 ∧
    (C.zeros.map (Quad.ranBag (inverse m))).sum = total + quartet m C.params.b 1 := by
  apply Zero.inventories m C.two_ne _ _ C.params.index.1 _ _ _ _ C.v_mem
  have := C.params.index.2
  have := C.q_eq
  omega

include C in
private theorem missing_eq_w₀ : ((missing (residueCase p) q : ℤ) : ZMod p) =
    (Translations.w₀ p q : ZMod p) := by
  have hq : 2 ≤ q := by have := C.q_eq; have := C.large; omega
  by_cases h : p % 3 = 1 <;> simp [residueCase, Translations.w₀, missing, h, Nat.cast_sub hq]

include C in
private theorem tableSize : InRange (residueCase p) (q : ℤ) := by
  have := C.q_eq
  have := C.large
  unfold residueCase
  split <;> simp only [InRange] <;> omega

private theorem tally {A : Type*} [AddCommMonoid A]
    (fibers joins translations zeros ends gap endpoint ord trans zero : A)
    (hf : fibers + ends + gap = ord) (he : ends = joins + endpoint)
    (ht : translations = trans + endpoint) (hz : zeros = zero + gap) :
    fibers + (joins + (translations + zeros)) = trans + zero + ord := by
  rw [ht,hz,← hf,he]
  ac_rfl

/-- Proposition 5.7 for the chosen orders and any final sign at each fiber. -/
def complete (switch : ℕ → Bool) (hc : C.CoversOrders) : Complete m (C.Row switch) := by
  apply completeOfInventory m (C.row switch) (C.closed switch)
  all_goals rw [C.row_sum, hc]
  · apply tally
      (ends := ∑ i, quartet m (C.last i) (coord i))
      (gap := quartet m C.params.a 1) (endpoint := quartet m C.special.E ((q - 1 : ℕ) : ZMod p))
    · have h (i : Fin (q - 1)) := (fiberRows_counts m C.two_ne (coord i) (switch (i.val+1))
          (C.first i) (C.last i) C.params.a C.params.b (C.middle i) (decide (i.val = 0))).1
      have allEq := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => h i)
      simpa only [ordinary, order, Finset.sum_add_distrib, C.single_gap] using allEq
    · exact last_blocks m C.special.K C.special.N C.special.E _ (by
        have := C.q_eq
        have := C.large
        omega)
    · exact Translations.dom_inventory ..
    · exact C.zero_inventory.1
  · apply tally
      (ends := ∑ i, quartet m (C.first i) (coord i))
      (gap := quartet m C.params.b 1)
      (endpoint := quartet m C.special.E (Translations.w₀ p q : ZMod p))
    · have h (i : Fin (q - 1)) := (fiberRows_counts m C.two_ne (coord i) (switch (i.val+1))
          (C.first i) (C.last i) C.params.a C.params.b (C.middle i) (decide (i.val = 0))).2
      have allEq := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => h i)
      simpa only [ordinary, order, Finset.sum_add_distrib, C.single_gap] using allEq
    · rw [← C.missing_eq_w₀]
      exact first_blocks m C.special.K C.special.N C.special.E _ (by
        have := C.q_eq
        have := C.large
        omega) C.tableSize
    · exact Translations.ran_inventory m _ _ _ _ C.two_ne
    · exact C.zero_inventory.2

@[simp] theorem complete_row (switch : ℕ → Bool) (hc : C.CoversOrders) (i : C.Row switch) :
    (C.complete switch hc).row i = C.row switch i := rfl

theorem has_ordinary (switch : ℕ → Bool) (hc : C.CoversOrders) (i : Fin (q - 1))
    {Q : Quad (Frame p q)} (h : Q ∈ C.ordinary switch i) :
    ∃ j, (C.complete switch hc).row j = Q := by
  obtain ⟨j,hj⟩ := List.get_of_mem h
  exact ⟨.inl ⟨i,j⟩, hj⟩

theorem has_join (switch : ℕ → Bool) (hc : C.CoversOrders) (i : Fin (q - 2)) :
    ∃ j, (C.complete switch hc).row j = C.joins i :=
  ⟨.inr (.inl i), rfl⟩

theorem has_translation (switch : ℕ → Bool) (hc : C.CoversOrders)
    (i : Translations.Row (2 * C.M)) :
    ∃ j, (C.complete switch hc).row j = C.translations i :=
  ⟨.inr (.inr (.inl i)), rfl⟩

theorem has_zero (switch : ℕ → Bool) (hc : C.CoversOrders) {Q : Quad (Frame p q)}
    (h : Q ∈ C.zeros) : ∃ j, (C.complete switch hc).row j = Q := by
  obtain ⟨j,hj⟩ := List.get_of_mem h
  exact ⟨.inr (.inr (.inr j)), hj⟩

end BipartiteKneser.Family.Construction
