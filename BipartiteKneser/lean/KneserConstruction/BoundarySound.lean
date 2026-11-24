module

public import KneserConstruction.BoundaryCheck
public import Mathlib.Data.Fintype.EquivFin

/-! A first return at the cardinality of a finite set visits all its elements. -/

@[expose] public section

namespace BipartiteKneser.Boundary

open Function

private theorem firstHit_spec {n : Nat} [NeZero n] {f : Fin n → Fin n}
    (k : Nat) (x : Fin n) (ok : firstHit f k x = true) :
    f^[k] x = 0 ∧ ∀ j < k, f^[j] x ≠ 0 := by
  induction k generalizing x with
  | zero => exact ⟨by simpa [firstHit] using ok, by simp⟩
  | succ k ih =>
    obtain ⟨hx, h⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨he, hlt⟩ := ih (f x) h
    refine ⟨by simpa only [iterate_succ_apply] using he, ?_⟩
    intro j hj
    cases j with
    | zero => simpa using hx
    | succ j => exact (iterate_succ_apply f j x) ▸ hlt j (by omega)

/-- A first return after exactly `n` steps gives forward reachability between all `n` labels. -/
theorem oneCycle_of_firstHit {n : Nat} [NeZero n] {f : Fin n → Fin n}
    (ok : firstHit f (n - 1) (f 0) = true) : ∀ x y, ∃ k : ℕ, f^[k] x = y := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have ns : n - 1 + 1 = n := by omega
  obtain ⟨he, hlt⟩ := firstHit_spec _ _ ok
  have per : IsPeriodicPt f n 0 := by
    change f^[n] 0 = 0
    have h : f^[n - 1 + 1] 0 = 0 := he
    rwa [ns] at h
  have pos := per.minimalPeriod_pos hn
  have big : n ≤ minimalPeriod f 0 := by
    by_contra! small
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
    have hit := iterate_minimalPeriod (f := f) (x := (0 : Fin n))
    rw [hj, iterate_succ_apply] at hit
    exact hlt j (by omega) hit
  let walk (i : Fin n) := f^[i.val] 0
  have inj : Injective walk := fun i j h => Fin.ext <|
    iterate_injOn_Iio_minimalPeriod (lt_of_lt_of_le i.isLt big) (lt_of_lt_of_le j.isLt big) h
  intro x y
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective inj x
  obtain ⟨j, rfl⟩ := Finite.surjective_of_injective inj y
  refine ⟨j.val + (n - i.val), ?_⟩
  change f^[j.val + (n - i.val)] (f^[i.val] 0) = f^[j.val] 0
  rw [iterate_add_apply, ← iterate_add_apply f (n - i.val) i.val,
    Nat.sub_add_cancel i.isLt.le, per.eq]

end BipartiteKneser.Boundary
