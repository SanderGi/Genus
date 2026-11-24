import KneserConstruction.ReductionRoutes
import KneserConstruction.Boundary
import KneserConstruction.CoordinateMissing
import KneserConstruction.Family

/-! # Sections 6–7. Global reduction to the 54- or 62-element boundary -/

namespace BipartiteKneser.Reduction

open Boundary Orbit

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable {m : Multipliers p q} {ι : Type*}

/-- Choose all switches simultaneously from the checked Section 7 witness and
the interval realization. Any complete family realizing the local paths for these
switches induces a single cycle on its full connection set. -/
theorem exists_switches_oneCycle (c : Case) (q M : ℕ) (hq : 65 ≤ q) (hM : 16 ≤ M)
    (χ : ℕ → Bool) (total : ((List.range' 1 (q - 1)).map χ).count true = 2 * M) :
    ∃ sw : ℕ → Bool, ∀ {p : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
      {m : Multipliers p q} {ι : Type*} (F : Family.Complete m ι) (N E K : Fin q),
      LocalPaths c F N E K χ sw → OneCycle F.rho := by
  let chars := pattern c q χ
  let bits k := χ (start c + k)
  let word := wordAt bits (length c q)
  obtain ⟨many, parity⟩ :=
    interval_character_count word ((List.range (count c)).map chars.val.testBit)
      M hM (by cases c <;> simp [count]) ((partition_count c hq χ).trans total)
  obtain ⟨mask, a, b, _, realized, cycle⟩ :=
    exists_realized_oneCycle c chars word (by omega) parity
  obtain ⟨s, ha, hb⟩ := switches_of_realizes realized
  refine ⟨switches c q mask s, ?_⟩
  intro p _ _ _ m ι F N E K localPaths
  exact oneCycle_of_boundary localPaths hq ha hb cycle

/-- For the actual positive fibers the missing-pair count supplies the parity
and length hypotheses of the interval witness. Only row-level paths are needed. -/
theorem exists_family_switches (c : Case) (m : Multipliers p q) {M : ℕ} (hM : 16 ≤ M)
    (hp : p = 2 * q + 1) (hq : q = 4 * M + 1) :
    ∃ sw : ℕ → Bool, ∀ {ι : Type*} (F : Family.Complete m ι) (N E K : Fin q),
      LocalPaths c F N E K (Coordinates.missingBit p) sw → OneCycle F.rho := by
  have total := Coordinates.missingBit_count_list (r := 2 * M) m hp (by omega) (by omega)
  obtain ⟨sw, spec⟩ := exists_switches_oneCycle c q M (by omega) hM _ total
  exact ⟨sw, fun F N E K => spec F N E K⟩

/-- Apply the reduction to the rows of the Section 5 construction. -/
theorem exists_complete_oneCycle (C : Family.Construction m) (hc : C.CoversOrders)
    (paths : ∀ sw, LocalPaths (if p % 3 = 1 then .one else .two) (C.complete sw hc)
      C.special.N C.special.E C.special.K (Coordinates.missingBit p) sw) :
    ∃ sw, OneCycle (C.complete sw hc).rho := by
  have size : p = 2 * q + 1 := by have := C.p_eq; have := C.q_eq; omega
  obtain ⟨sw, lift⟩ := exists_family_switches (if p % 3 = 1 then .one else .two) m
    C.large size C.q_eq
  exact ⟨sw, lift _ _ _ _ (paths sw)⟩

end BipartiteKneser.Reduction
