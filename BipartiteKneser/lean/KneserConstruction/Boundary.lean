import KneserConstruction.BoundaryFinite
import KneserConstruction.BoundarySound
import KneserConstruction.BoundaryLabels

/-!
# The finite one-cycle witness (Section 7)

Proposition 7.3, in the forward transfer convention of Corollary 6.11.
The symbolic coordinate identification of Proposition 7.2 is `normalize_step`.
-/

namespace BipartiteKneser.Boundary

/-- Every formal sign assignment admits a listed outside switch mask and a pair
of forward interval transfers of the required sign, giving one cycle. -/
theorem exists_oneCycle (c : Case) (chars : Pattern c) :
    ∃ (mask : Nat) (p r : Interval.Perm), mask ∈ choices c ∧
      (Interval.odd p ^^ Interval.odd r) = positiveParity c chars ∧
      ∀ x y, ∃ n : ℕ, (step c chars mask p r)^[n] x = y := by
  obtain ⟨v, ok⟩ := check_all c chars
  obtain ⟨hm, hp, hc⟩ := check_sound ok
  exact ⟨_, _, _, hm, hp, oneCycle_of_firstHit hc⟩

/-- Apply Lemma 6.10 to the forward codes returned by Proposition 7.3. -/
theorem exists_realized_oneCycle (c : Case) (chars : Pattern c) (word : List Bool)
    (five : 5 ≤ word.count true) (par : Interval.parity word = positiveParity c chars) :
    ∃ (mask : Nat) (p r : Interval.Perm), mask ∈ choices c ∧ Interval.Realizes word p r ∧
      ∀ x y, ∃ n : ℕ, (step c chars mask p r)^[n] x = y := by
  obtain ⟨mask, p, r, hm, hp, hc⟩ := exists_oneCycle c chars
  exact ⟨mask, p, r, hm, (Interval.realizes_iff_of_five five p r).2 (hp.trans par.symm), hc⟩

end BipartiteKneser.Boundary
