module

public import KneserConstruction.CriterionCard
public import KneserConstruction.CriterionCycle
public import KneserConstruction.CriterionRows
public import BipartiteKneser.Certificates

/-! # Section 3. A complete admissible family with one orbit gives a quadrangulation -/

@[expose] public section

namespace BipartiteKneser.Criterion

open Family

variable {p q d : ℕ} [NeZero p] [NeZero q] [NeZero d]
variable {m : Multipliers p q} {ι : Type*}

private noncomputable def base (m : Multipliers p q) (e : Fin d ≃ Label m) : BaseCycle p q d where
  scale := m.power
  label i := (e i).val
  index s := if hs : separated m.power s = true then e.symm ⟨s, hs⟩ else 0

private theorem covers (e : Fin d ≃ Label m) : (base m e).Covers := by
  refine ⟨fun i => (e i).property, fun i => ?_, fun s hs => ?_⟩
  · simp [base, (e i).property]
  · change separated m.power s = true at hs
    simp [base, hs]

/-- A nontrivial successor or predecessor at the head prevents a two-step
return to the same frame, in either bipartition class. -/
private theorem diagonal (c : BaseCycle p q d) (scale : c.scale = m.power) (cv : c.Covers)
    (hd : 1 < d) (b : Bool) (i : Fin d) :
    compose c.scale (c.label i) (c.label (c.nextIndex b i)) ≠ (0, 0) := by
  have oneNe : (1 : Fin d) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt hd] at this
  intro he
  have invEq : inverse m (c.label i) = c.label (c.nextIndex b i) := by
    apply @inv_eq_of_mul_eq_one_right (AffineFrame m) _ (c.label i) (c.label (c.nextIndex b i))
    change compose m.power _ _ = (0, 0)
    rwa [← scale]
  have rev : c.reverseIndex i = c.nextIndex b i := by
    have eq := congrArg c.index invEq
    change c.index (inverse m (c.label i)) = _ at eq
    simpa only [BaseCycle.reverseIndex, inverse, scale, cv.unique] using eq
  apply oneNe
  cases b
  · change c.reverseIndex i = c.reverseIndex i - 1 at rev
    simpa using (sub_eq_self.mp rev.symm)
  · change c.reverseIndex i = c.reverseIndex i + 1 at rev
    simpa using (add_left_cancel (a := c.reverseIndex i) (rev.symm.trans (add_zero _).symm))

private theorem checks (F : Complete m ι) (e : Fin d ≃ Label m)
    (step : ∀ i, e (i + 1) = F.rho (e i)) (hd : 1 < d) :
    ∀ part i, (base m e).checkFace part i = true := by
  let c := base m e
  have cv := covers e
  have pw : c.Powers := ⟨m.zero, m.add⟩
  let D (k : ι) (u v : Bool) := e.symm (F.domain (k, u, v))
  let R (k : ι) (u v : Bool) := e.symm (F.range (k, u, v))
  have labD (k u v) : c.label (D k u v) = (F.row k).dom (inverse m) (u, v) := by
    simpa [c, D, base] using F.domain_val k (u, v)
  have labR (k u v) : c.label (R k u v) = (F.row k).ran (inverse m) (u, v) := by
    simpa [c, R, base] using F.range_val k (u, v)
  have succD (k u v) : D k u v + 1 = R k u v := by
    apply e.injective
    simp [step, D, R]
  have predR (k u v) : R k u v - 1 = D k u v := by rw [← succD]; simp
  have labelInj : Function.Injective c.label := Subtype.val_injective.comp e.injective
  have invInv (s : Frame p q) : inverse m (inverse m s) = s := @inv_inv (AffineFrame m) _ s
  have nextD (k u v) : c.nextIndex true (D k u v) = R k u (!v) := by
    have rev : c.reverseIndex (D k u v) = D k u (!v) := by
      apply labelInj
      rw [c.label_reverse pw cv]
      change inverse m (c.label (D k u v)) = c.label (D k u (!v))
      rw [labD, labD]
      cases u <;> cases v <;> simp [Quad.dom, invInv]
    exact (congrArg (· + 1) rev).trans (succD ..)
  have nextR (k u v) : c.nextIndex false (R k u v) = D k (!u) v := by
    have rev : c.reverseIndex (R k u v) = R k (!u) v := by
      apply labelInj
      rw [c.label_reverse pw cv]
      change inverse m (c.label (R k u v)) = c.label (R k (!u) v)
      rw [labR, labR]
      cases u <;> cases v <;> simp [Quad.ran, invInv]
    exact (congrArg (· - 1) rev).trans (predR ..)
  intro part i
  change c.checkFace part i = true
  simp only [BaseCycle.checkFace, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  refine ⟨⟨?_, diagonal c rfl cv hd part i⟩, diagonal c rfl cv hd (!part) _⟩
  cases part
  · obtain ⟨⟨k, u, v⟩, hi⟩ := F.range.surjective (e i)
    have ix : i = R k u v := e.injective (by simpa [R] using hi.symm)
    rw [ix]
    simp only [Bool.not_false, Bool.not_not, nextR, nextD, labR, labD, and_true]
    exact (row_products (G := AffineFrame m) (F.row k) (F.closed k) u v).1
  · obtain ⟨⟨k, u, v⟩, hi⟩ := F.domain.surjective (e i)
    have ix : i = D k u v := e.injective (by simpa [D] using hi.symm)
    rw [ix]
    simp only [Bool.not_true, Bool.not_not, nextD, nextR, labD, labR, and_true]
    exact (row_products (G := AffineFrame m) (F.row k) (F.closed k) u v).2

/-- Lemma 3.5 with the actual degree of the two-subset graph. Completeness gives
the four-step equations and the single orbit supplies the cyclic local order. -/
theorem of_complete [NeZero ((p - 2) * (p - 3) / 2)] (hp : 5 ≤ p) (F : Complete m ι)
    (orbit : ∀ x y, ∃ n : ℕ, F.rho^[n] x = y) :
    HasAffineQuadrangulation p q ((p - 2) * (p - 3) / 2) := by
  obtain ⟨e, step⟩ := exists_cyclic_index F.rho orbit (card_label m (by omega))
  have hd : 1 < (p - 2) * (p - 3) / 2 := by
    have := Nat.mul_le_mul (show 3 ≤ p - 2 by omega) (show 2 ≤ p - 3 by omega)
    omega
  exact of_certificate (base m e) (m.chart _ rfl) ⟨m.zero, m.add⟩ (covers e) (checks F e step hd)

end BipartiteKneser.Criterion
