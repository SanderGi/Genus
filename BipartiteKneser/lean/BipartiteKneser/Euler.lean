import Std

/-!
# Euler bound for H(h,2)

In a cellular embedding, summing the face lengths gives twice the number of
edges. For the bipartite graph in the paper, all face lengths are at least four.
This module proves the numerical implication of these two counts and Euler's
equation, including the equality criterion. All calculations use integers.
-/

set_option linter.all true

namespace BipartiteKneser

/-- The genus in Theorem 1.1, with subtraction in the integers. -/
def genusFormula (h : Int) : Int :=
  1 - h * (h - 1) / 2 + h * (h - 1) * (h - 2) * (h - 3) / 16

/-- Product form of the Euler bound and the equivalent binomial form. -/
theorem genusFormula_eq (h : Int) (residue : h % 8 = 3) :
    genusFormula h = 1 + (h * (h - 1) / 2) * ((h - 2) * (h - 3) / 2 - 4) / 4 := by
  let t := h / 8
  have ht : h = 8*t + 3 := by dsimp [t]; omega
  have h₁ : h * (h - 1) = 2 * ((8*t+3) * (4*t+1)) := by rw [ht]; grind
  have h₂ : (h - 2) * (h - 3) = 8 * ((8*t+1)*t) := by rw [ht]; grind
  have h₃ : h * (h - 1) * (h - 2) * (h - 3) =
      16 * (((8*t+3)*(4*t+1))*((8*t+1)*t)) := by rw [ht]; grind
  unfold genusFormula
  rw [h₃, h₁, h₂]
  generalize (8*t+3)*(4*t+1) = n
  generalize (8*t+1)*t = k
  have hd : 8*k / 2 = 4*k := by omega
  rw [hd]
  have hp : n * (4*k-4) = 4*(n*k-n) := by grind
  simp only [Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]
  rw [hp]
  omega

/-- Euler's lower bound using V = h(h−1), 4E = h(h−1)(h−2)(h−3),
and 4F ≤ 2E. Equality holds precisely when 4F = 2E. -/
theorem euler_bound (h edges faces genus : Int) (residue : h % 8 = 3)
    (edgeCount : 4 * edges = h * (h - 1) * (h - 2) * (h - 3))
    (euler : 2 - 2 * genus = h * (h - 1) - edges + faces)
    (faceBound : 4 * faces ≤ 2 * edges) :
    genusFormula h ≤ genus ∧ (genus = genusFormula h ↔ 4 * faces = 2 * edges) := by
  let t := h / 8
  have ht : h = 8*t + 3 := by dsimp [t]; omega
  have h₁ : h * (h - 1) = 2 * ((8*t+3) * (4*t+1)) := by rw [ht]; grind
  have h₂ : h * (h - 1) * (h - 2) * (h - 3) =
      16 * (((8*t+3)*(4*t+1))*((8*t+1)*t)) := by rw [ht]; grind
  unfold genusFormula
  omega

end BipartiteKneser
