module

public import KneserConstruction.FamilyCore

/-!
# Counting assignments when replacing quadruples

The inventories are multisets, so equality records the multiplicity of each
dart even when two written expressions denote the same affine frame.
-/

@[expose] public section

namespace BipartiteKneser.Family

variable {α ι : Type*}

/-- Both orientations of an inverse pair, counted with multiplicity. -/
def pair (inv : α → α) (x : α) : Multiset α := {x} + {inv x}

/-- Domain inventory of a quadruple. -/
def Quad.domBag (inv : α → α) (Q : Quad α) := pair inv Q.a + pair inv Q.b

/-- Range inventory of a quadruple. -/
def Quad.ranBag (inv : α → α) (Q : Quad α) := pair inv Q.c + pair inv Q.d

theorem pair_inverse (inv : α → α) (h : Function.Involutive inv) (x : α) :
    pair inv (inv x) = pair inv x := by simp [pair, h x, add_comm]

private theorem sum_slot (f : Slot → Multiset α) :
    ∑ s, f s = f (false,false) + f (false,true) + f (true,false) + f (true,true) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ac_rfl

theorem Quad.dom_inventory (inv : α → α) (Q : Quad α) :
    ∑ s, ({Quad.dom inv Q s} : Multiset α) = Q.domBag inv := by
  rw [sum_slot]
  unfold Quad.domBag pair
  dsimp only [Quad.dom]
  ac_rfl

theorem Quad.ran_inventory (inv : α → α) (Q : Quad α) :
    ∑ s, ({Quad.ran inv Q s} : Multiset α) = Q.ranBag inv := by
  rw [sum_slot]
  unfold Quad.ranBag pair
  dsimp only [Quad.ran]
  ac_rfl

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- Each separated frame occurs exactly once. -/
def inventory (m : Multipliers p q) : Multiset (Frame p q) :=
  ((Finset.univ : Finset (Label m)).val.map Subtype.val)

theorem map_univ_eq_sum [Fintype ι] (f : ι → α) :
    Finset.univ.val.map f = ∑ i, ({f i} : Multiset α) := by
  rw [← Finset.sum_multiset_singleton (Finset.univ : Finset ι)]
  exact (map_sum (Multiset.mapAddMonoidHom f) _ _)

/-- A single occurrence of each separated label gives an equivalence with the row slots. -/
noncomputable def equivOfInventory (m : Multipliers p q) [Fintype ι]
    (f : ι → Frame p q) (hf : (∑ i, ({f i} : Multiset _)) = inventory m) :
    ι ≃ Label m := by
  classical
  rw [← map_univ_eq_sum] at hf
  have mem (i : ι) : f i ∈ inventory m := hf ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have ok (i : ι) : separated m.power (f i) = true := by
    obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp (mem i)
    exact hx ▸ x.property
  refine Equiv.ofBijective (fun i => ⟨f i, ok i⟩) ⟨?_, ?_⟩
  · have nd : (inventory m).Nodup :=
      (Finset.univ.nodup.map (f := (Subtype.val : Label m → _)) Subtype.val_injective)
    rw [← hf, Multiset.nodup_map_iff_inj_on Finset.univ.nodup] at nd
    intro i j eq
    exact nd i (Finset.mem_univ_val _) j (Finset.mem_univ_val _) (congrArg Subtype.val eq)
  · intro x
    have hm : x.val ∈ inventory m := Multiset.mem_map_of_mem _ (Finset.mem_univ_val x)
    rw [← hf, Multiset.mem_map] at hm
    obtain ⟨i, _, hi⟩ := hm
    exact ⟨i, Subtype.ext hi⟩

/-- Assemble a complete family from row closure and exact domain/range counts. -/
noncomputable def completeOfInventory (m : Multipliers p q) [Fintype ι]
    (row : ι → Quad (Frame p q))
    (closed : ∀ i, compose m.power (row i).a (row i).c = compose m.power (row i).d (row i).b)
    (dom : ∑ i, (row i).domBag (inverse m) = inventory m)
    (ran : ∑ i, (row i).ranBag (inverse m) = inventory m) : Complete m ι where
  row := row
  closed := closed
  domain := equivOfInventory m (fun t : ι × Slot => Quad.dom (inverse m) (row t.1) t.2)
    (by rw [Fintype.sum_prod_type]; simpa only [Quad.dom_inventory] using dom)
  range := equivOfInventory m (fun t : ι × Slot => Quad.ran (inverse m) (row t.1) t.2)
    (by rw [Fintype.sum_prod_type]; simpa only [Quad.ran_inventory] using ran)
  domain_val _ _ := rfl
  range_val _ _ := rfl

end BipartiteKneser.Family
