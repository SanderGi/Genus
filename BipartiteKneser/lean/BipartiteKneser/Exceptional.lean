import KneserWitnessData

/-!
# Exceptional primes

Proposition 8.1 of *The Genus of Bipartite Kneser Graphs*. The generated
module supplies numeric tables. Only their checked mathematical properties
are used to establish the existence theorems below.
-/

set_option linter.all true

namespace BipartiteKneser.Exceptional

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

-- Check bounded quantifiers in small independent kernel reductions.
private def Block {n : Nat} [NeZero n] (P : Fin n → Prop) (start len : Nat) :=
  ∀ j : Fin len, P (Fin.ofNat n (start + j.val))

private theorem of_block {n : Nat} [NeZero n] {P : Fin n → Prop} (b : Block P 0 n) :
    ∀ i, P i := by
  intro i
  simpa [Fin.ofNat, Nat.mod_eq_of_lt i.isLt] using b i

private theorem split_block {n : Nat} [NeZero n] {P : Fin n → Prop} {start len : Nat}
    (left : Block P start (len / 2))
    (right : Block P (start + len / 2) (len - len / 2)) : Block P start len := by
  intro j
  by_cases h : j.val < len / 2
  · exact left ⟨j.val, h⟩
  · have hj := j.isLt
    have hv : start + len / 2 + (j.val - len / 2) = start + j.val := by omega
    simpa only [hv] using right ⟨j.val - len / 2, by omega⟩

local macro "check_indices " depth:num : tactic =>
  `(tactic| (
    apply of_block
    iterate $depth (all_goals apply split_block)
    all_goals unfold Block
    all_goals as_aux_lemma => decide +kernel))

local macro "verify_cycle " c:term " using " dec:term " depth " depth:num : tactic =>
  `(tactic| (
    apply of_certificate $c (by
      exact {
        decode := $dec
        increasing := by rw [Prod.forall]; decide +kernel
        leftInv := by rw [Prod.forall]; decide +kernel
        rightInv := by decide +kernel })
    · constructor <;> decide +kernel
    · constructor
      · check_indices $depth
      · check_indices $depth
      · rw [Prod.forall]; decide +kernel
    · intro part
      cases part <;> check_indices $depth))

/-- The Section 8 rotation for H(11,2). -/
theorem case11 : HasAffineQuadrangulation 11 5 36 := by
  verify_cycle cycle11 using decode11 depth 0

/-- The Section 8 rotation for H(19,2). -/
theorem case19 : HasAffineQuadrangulation 19 9 136 := by
  verify_cycle cycle19 using decode19 depth 1

/-- The Section 8 rotation for H(43,2). -/
theorem case43 : HasAffineQuadrangulation 43 21 820 := by
  verify_cycle cycle43 using decode43 depth 4

/-- The Section 8 rotation for H(59,2). -/
theorem case59 : HasAffineQuadrangulation 59 29 1596 := by
  verify_cycle cycle59 using decode59 depth 5

/-- The Section 8 rotation for H(67,2). -/
theorem case67 : HasAffineQuadrangulation 67 33 2080 := by
  verify_cycle cycle67 using decode67 depth 5

/-- The Section 8 rotation for H(83,2). -/
theorem case83 : HasAffineQuadrangulation 83 41 3240 := by
  verify_cycle cycle83 using decode83 depth 6

/-- The Section 8 rotation for H(107,2). -/
theorem case107 : HasAffineQuadrangulation 107 53 5460 := by
  verify_cycle cycle107 using decode107 depth 7

end BipartiteKneser.Exceptional
