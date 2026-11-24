module

public import KneserConstruction.OrbitCore
public import BipartiteKneser.Interval
import Mathlib.Tactic.FinCases

/-! # Expanding the six transfers across the ordinary interval -/

@[expose] public section

namespace BipartiteKneser.Orbit

open BipartiteKneser.Interval

/-- Fiber offsets increase from zero. The interval automaton prepends each new bit. -/
def wordAt (character : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => character n :: wordAt character n

/-- At coordinate sign minus the character bit toggles the positive-strand switch. -/
def strandSwitch (switch character minus : Bool) := switch ^^ (minus && character)

/-- Forward composite on one triple after the first n fibers. -/
def forward (character switch : ℕ → Bool) (minus : Bool) : ℕ → Perm
  | 0 => 0
  | n + 1 => step (strandSwitch (switch n) (character n) minus) (forward character switch minus n)

private theorem forward_congr {χ s t : ℕ → Bool} {n : ℕ} (he : ∀ k < n, s k = t k)
    (minus : Bool) : forward χ s minus n = forward χ t minus n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forward, forward, he n (by omega), ih (fun k hk => he k (by omega))]

/-- Extract independently addressable switches from the existing interval certificate. -/
theorem switches_of_realizes {χ : ℕ → Bool} {n : ℕ} {p q : Perm}
    (h : Realizes (wordAt χ n) p q) :
    ∃ s : ℕ → Bool, forward χ s false n = p ∧ forward χ s true n = q := by
  induction n generalizing p q with
  | zero =>
    cases h
    exact ⟨fun _ => false, rfl, rfl⟩
  | succ n ih =>
    cases h with
    | cons r a b =>
      obtain ⟨s, hp, hq⟩ := ih r
      let t k := if k = n then b else s k
      have he (minus) : forward χ t minus n = forward χ s minus n :=
        forward_congr (fun k hk => by simp [t, show k ≠ n by omega]) minus
      exact ⟨t, by simp [forward, he, t, strandSwitch, hp],
        by simp [forward, he, t, strandSwitch, hq]⟩

/-- The bounded witness's two forward maps are simultaneously realizable. -/
theorem exists_switches {χ : ℕ → Bool} {n : ℕ} {p q : Perm}
    (many : 5 ≤ (wordAt χ n).count true) (sign : (odd p ^^ odd q) = parity (wordAt χ n)) :
    ∃ s : ℕ → Bool, forward χ s false n = p ∧ forward χ s true n = q :=
  switches_of_realizes ((realizes_iff_of_five many p q).mpr sign)

/-- Slot order within a triple. Slot 2 belongs to the following fiber. -/
def localImage (b : Bool) (i : Fin 3) := image (if b then 4 else 1) i

/-- A transition of the uncontracted permutation on the two current slots implies
the full three-slot transfer, including the shared vertex in slot 2. -/
theorem triple_step {α : Type*} {f : α → α} {A B : Fin 3 → α} {b : Bool}
    (left : Reach f (A 0) (B (if b then 2 else 0)))
    (right : Reach f (A 1) (B (if b then 0 else 2))) (shared : A 2 = B 1) :
    Across f A B (localImage b) := by
  intro i
  fin_cases i <;> cases b <;> first | exact left | exact right | exact ⟨0, shared⟩

/-- Chaining the local strand diagrams yields entry-to-exit paths for the precise
forward codes chosen by the bounded certificate. -/
theorem interval_paths {α : Type*} {f : α → α} {χ s : ℕ → Bool} {n : ℕ}
    (layer : ℕ → Bool → Fin 3 → α)
    (localPaths : ∀ k < n, ∀ minus, Across f (layer k minus) (layer (k + 1) minus)
      (localImage (strandSwitch (s k) (χ k) minus))) (minus : Bool) :
    Across f (layer 0 minus) (layer n minus) (image (forward χ s minus n)) := by
  induction n with
  | zero =>
    intro i
    have id0 : ∀ i : Fin 3, image 0 i = i := by decide
    simpa [forward, id0] using Reach.refl (f := f) (layer 0 minus i)
  | succ n ih =>
    intro i
    rw [forward, image_step]
    exact (ih (fun k hk => localPaths k (by omega)) i).trans
      (localPaths n (by omega) minus _)

/-- Lemma 7.1 expressed using the actual bit words at the interval and the boundary. -/
theorem interval_character_count (inside outside : List Bool) (M : ℕ) (large : 16 ≤ M)
    (bound : outside.length ≤ 14) (total : inside.count true + outside.count true = 2 * M) :
    18 ≤ inside.count true ∧ parity inside = parity outside := by
  have hb := List.count_le_length (a := true) (l := outside)
  have count_parity (w : List Bool) : parity w = (w.count true % 2 == 1) := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      cases a <;> simp [parity, ih]
      have bit : (w.count true + 1) % 2 = 1 ↔ w.count true % 2 = 0 := by omega
      by_cases he : w.count true % 2 = 0 <;> simp_all
  constructor
  · omega
  · rw [count_parity, count_parity, show inside.count true % 2 = outside.count true % 2 by omega]

end BipartiteKneser.Orbit
