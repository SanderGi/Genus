module

public import BipartiteKneser.SmallPrimes
public import KneserConstruction.AdmissiblePrimes
public import KneserConstruction.Criterion
public import KneserConstruction.Orbit
public import KneserConstruction.Uniform

/-! # Theorem 1.1 of *The Genus of Bipartite Kneser Graphs* -/

@[expose] public section

namespace BipartiteKneser

/-- The finite certificate checker uses exactly mathlib's notion of primality. -/
theorem prime_iff_natPrime (p : ℕ) : Prime p ↔ p.Prime := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨lo, h⟩
    exact ⟨lo, fun k hk lt dv => h ⟨k, lt⟩ hk (Nat.mod_eq_zero_of_dvd dv)⟩
  · rintro ⟨lo, h⟩
    exact ⟨lo, fun k hk z => h k.val hk k.isLt (Nat.dvd_of_mod_eq_zero z)⟩

/-- Sections 4–7 construct a vertex-transitive orientable quadrangulation for every
admissible prime at least 131. -/
theorem quadrangulation_of_le {p : ℕ} [Fact p.Prime] (large : 131 ≤ p) (res : p % 8 = 3)
    [NeZero p] [NeZero ((p - 1) / 2)] [NeZero ((p - 2) * (p - 3) / 2)] :
    HasAffineQuadrangulation p ((p - 1) / 2) ((p - 2) * (p - 3) / 2) := by
  let q := (p - 1) / 2
  let M := p / 8
  have hM : 16 ≤ M := by dsimp [M]; omega
  have hp : p = 8 * M + 3 := by dsimp [M]; omega
  have hq : q = 4 * M + 1 := by dsimp [q, M]; omega
  have size : p = 2 * q + 1 := by omega
  obtain ⟨m⟩ := Multipliers.exists_of_prime p q size (by omega)
  obtain ⟨C, _, covers, length⟩ := Family.exists_construction m hM hp hq
  have parity (i : Fin (q - 1)) :
      ((C.middle i).length % 2 == 0) = !(Coordinates.missingBit p (i.val + 1)) :=
    Bool.eq_iff_iff.mpr (by simpa using length i)
  obtain ⟨sw, orbit⟩ := Orbit.exists_oneCycle C covers parity
  exact Criterion.of_complete (by omega) (C.complete sw covers) orbit

/-- Theorem 1.1. Every prime h > 3 congruent to 3 modulo 8 admits a vertex-transitive
quadrangular rotation system on H(h,2) attaining its minimum orientable genus. -/
theorem optimalRotation_of_prime {h : ℕ} (prime : h.Prime) (large : 3 < h)
    (residue : h % 8 = 3) : OptimalRotation h := by
  by_cases small : h < 131
  · exact optimalRotation_of_lt_131 ((prime_iff_natPrime h).mpr prime) large residue small
  have : Fact h.Prime := ⟨prime⟩
  have : NeZero h := ⟨by omega⟩
  have : NeZero ((h - 1) / 2) := ⟨by omega⟩
  have : NeZero ((h - 2) * (h - 3) / 2) := ⟨by
    have bound := Nat.mul_le_mul (show 2 ≤ h - 2 by omega) (show 2 ≤ h - 3 by omega)
    omega⟩
  exact optimal_of_quadrangulation large residue (quadrangulation_of_le (by omega) residue)

/-- The primes realizing the embeddings of Theorem 1.1 are unbounded. -/
theorem exists_optimalRotation_gt (n : ℕ) :
    ∃ h > n, h.Prime ∧ 3 < h ∧ h % 8 = 3 ∧ OptimalRotation h := by
  obtain ⟨h, gt, prime, residue⟩ := exists_admissible_prime_gt (max n 3)
  exact ⟨h, by omega, prime, by omega, residue, optimalRotation_of_prime prime (by omega) residue⟩

end BipartiteKneser
