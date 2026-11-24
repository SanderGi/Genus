module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Infinitely many admissible primes

For the Euclidean argument, take the product of the squares of all candidate
residues `8i+3` up to the cutoff. Its square plus two is three modulo eight.
Every prime divisor represents −2 as a square, so at least one is three modulo
eight. It cannot divide the original product.
-/

public section

namespace BipartiteKneser

/-- The primes congruent to three modulo eight exceed every natural bound. -/
theorem exists_admissible_prime_gt (n : ℕ) : ∃ p > n, p.Prime ∧ p % 8 = 3 := by
  let x := ∏ i ∈ Finset.range (n + 1), (8 * i + 3) ^ 2
  have hx : x ≡ 1 [MOD 8] := by
    apply Nat.ModEq.prod_one
    intro i _
    have h : 8 * i + 3 ≡ 3 [MOD 8] := by change (8 * i + 3) % 8 = 3; omega
    exact (h.pow 2).trans (by decide)
  let y := x ^ 2 + 2
  have hy : y % 8 = 3 := (hx.pow 2).add_right 2
  have hy₀ : y ≠ 0 := by omega
  have residues (d : ℕ) (hd : d ∈ y.primeFactorsList) : d % 8 = 1 ∨ d % 8 = 3 := by
    obtain ⟨prime, dvd⟩ := (Nat.mem_primeFactorsList hy₀).mp hd
    have : Fact d.Prime := ⟨prime⟩
    have ne : d ≠ 2 := by
      rintro rfl
      omega
    have he := (ZMod.natCast_eq_zero_iff y d).2 dvd
    have root : (x : ZMod d) ^ 2 + 2 = 0 := by simpa [y] using he
    apply (ZMod.exists_sq_eq_neg_two_iff ne).1
    exact ⟨x, by rw [← pow_two, ← eq_neg_of_add_eq_zero_left root]⟩
  obtain ⟨p, member, hp⟩ : ∃ p ∈ y.primeFactorsList, p % 8 = 3 := by
    by_contra! h
    have allOne : y.primeFactorsList.prod ≡ 1 [MOD 8] :=
      Nat.ModEq.listProd_one fun d hd => (residues d hd).resolve_right (h d hd)
    rw [Nat.prod_primeFactorsList hy₀] at allOne
    change y % 8 = 1 at allOne
    omega
  obtain ⟨prime, dvd⟩ := (Nat.mem_primeFactorsList hy₀).mp member
  refine ⟨p, ?_, prime, hp⟩
  by_contra! small
  have rep : 8 * (p / 8) + 3 = p := by omega
  have divides : p ^ 2 ∣ x := by
    have h := Finset.dvd_prod_of_mem (fun i => (8 * i + 3) ^ 2)
      (Finset.mem_range.mpr (show p / 8 < n + 1 by omega))
    simpa only [rep] using h
  have px : p ∣ x := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) divides
  have two : p ∣ 2 := (Nat.dvd_add_right (dvd_pow px (by decide : 2 ≠ 0))).mp dvd
  have := Nat.le_of_dvd (by decide : 0 < 2) two
  omega

end BipartiteKneser
