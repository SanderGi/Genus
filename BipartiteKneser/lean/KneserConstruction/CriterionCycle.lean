module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Fin.Basic

/-! # Indexing a single orbit by its positions modulo the cardinality -/

public section

namespace BipartiteKneser.Criterion

open Function

/-- Traversing a transitive map on a nonempty finite set gives the cyclic
enumeration needed by the affine rotation interface. -/
theorem exists_cyclic_index {α : Type*} [Fintype α] {d : ℕ} [NeZero d]
    (f : α → α) (orbit : ∀ x y, ∃ n : ℕ, f^[n] x = y) (card : Fintype.card α = d) :
    ∃ e : Fin d ≃ α, ∀ i, e (i + 1) = f (e i) := by
  classical
  have pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (card ▸ pos)
  obtain ⟨n, hn⟩ := orbit (f x) x
  have periodic : x ∈ periodicPts f := ⟨n + 1, by omega, by
    simpa only [IsPeriodicPt, IsFixedPt, iterate_succ_apply] using hn⟩
  have periodPos := minimalPeriod_pos_of_mem_periodicPts periodic
  let walk (i : Fin (minimalPeriod f x)) := f^[i.val] x
  have bij : Bijective walk := by
    constructor
    · intro i j he
      exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp he)
    · intro y
      obtain ⟨k, hk⟩ := orbit x y
      exact ⟨⟨k % minimalPeriod f x, Nat.mod_lt _ periodPos⟩, iterate_mod_minimalPeriod_eq.trans hk⟩
  let e := Equiv.ofBijective walk bij
  have period : minimalPeriod f x = d := by
    simpa only [Fintype.card_fin, card] using Fintype.card_congr e
  refine ⟨(finCongr period.symm).trans e, fun i => ?_⟩
  change f^[(i + 1).val] x = f (f^[i.val] x)
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, ← iterate_succ_apply' f i.val x]
  simpa only [period] using (iterate_mod_minimalPeriod_eq (f := f) (x := x) (n := i.val + 1))

end BipartiteKneser.Criterion
