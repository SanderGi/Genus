import KneserConstruction.FamilyCore
import Mathlib.Tactic.Group

/-! # The group equations for the four orientations of a row -/

namespace BipartiteKneser.Criterion
open Family

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- Frames with composition determined by a fixed multiplier table. -/
def AffineFrame (_m : Multipliers p q) := Frame p q

instance (m : Multipliers p q) : Group (AffineFrame m) where
  mul := compose m.power
  inv := inverse m
  one := (0, 0)
  mul_assoc x y z := by
    change compose _ (compose _ x y) z = compose _ x (compose _ y z)
    apply Prod.ext <;> simp [compose, m.add] <;> grind
  one_mul x := by
    change compose _ (0, 0) x = x
    cases x
    simp [compose, m.zero]
  mul_one x := by
    change compose _ x (0, 0) = x
    cases x
    simp [compose]
  inv_mul_cancel x := by
    change compose _ (inverse m x) x = (0, 0)
    simp [compose, inverse]

section
variable {G : Type*} [Group G]

/-- Starting on the range side of a row, inversion switches the first bit;
on the domain side it switches the second bit. -/
theorem row_products (Q : Quad G) (closed : Q.a * Q.c = Q.d * Q.b) (u v : Bool) :
    (Q.ran Inv.inv (u, v) * Q.dom Inv.inv (!u, v) *
      Q.ran Inv.inv (!u, !v) * Q.dom Inv.inv (u, !v) = 1) ∧
    (Q.dom Inv.inv (u, v) * Q.ran Inv.inv (u, !v) *
      Q.dom Inv.inv (!u, !v) * Q.ran Inv.inv (!u, v) = 1) := by
  have hd : Q.d = Q.a * Q.c * Q.b⁻¹ := by rw [closed, mul_inv_cancel_right]
  cases u <;> cases v <;> constructor <;> simp only [Bool.not_false, Bool.not_true,
    Quad.dom, Quad.ran, hd] <;> group

end

end BipartiteKneser.Criterion
