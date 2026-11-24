import BipartiteKneser.Exceptional
import BipartiteKneser.Genus

/-! # The minimum genus and optimal rotations for the exceptional primes -/

namespace BipartiteKneser

/-- Primality expressed by trial divisors strictly between 1 and h. -/
def Prime (h : Nat) : Prop := 2 ≤ h ∧ ∀ k : Fin h, 2 ≤ k.val → h % k.val ≠ 0

private theorem small_cases : ∀ n : Fin 131, 3 < n.val → n.val % 8 = 3 → Prime n.val →
    n.val = 11 ∨ n.val = 19 ∨ n.val = 43 ∨ n.val = 59 ∨ n.val = 67 ∨ n.val = 83 ∨
    n.val = 107 := by
  unfold Prime
  decide +kernel

/-- Theorem 1.1 for every admissible prime below 131. -/
theorem optimalRotation_of_lt_131 {h : Nat} (prime : Prime h) (large : 3 < h)
    (residue : h % 8 = 3) (small : h < 131) : OptimalRotation h := by
  rcases small_cases ⟨h, small⟩ large residue prime with eq | eq | eq | eq | eq | eq | eq
  all_goals change h = _ at eq
  all_goals subst h
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case11
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case19
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case43
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case59
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case67
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case83
  · exact optimal_of_quadrangulation (by decide) (by decide) Exceptional.case107

end BipartiteKneser
