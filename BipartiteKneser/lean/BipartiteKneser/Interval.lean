import Std

/-!
# Transfers on the three strands of each sign

Proposition 6.9 and Lemma 6.10 of *The Genus of Bipartite Kneser Graphs*.
The local maps act on the left, in the forward (entry-to-exit) convention.
The finite automaton below tracks the exact set of attainable pairs. Its
transition table is checked against the two permutations at a single fiber.
-/

namespace BipartiteKneser.Interval

/-- Permutations of three positions, numbered by lexicographic order of their images. -/
abbrev Perm := Fin 6

/-- Image of a position under a transfer permutation. -/
def image (p : Perm) (i : Fin 3) : Fin 3 :=
  (#[#[0, 1, 2], #[0, 2, 1], #[1, 0, 2], #[1, 2, 0], #[2, 0, 1], #[2, 1, 0]][p.val]!)[i.val]!

/-- These codes enumerate exactly the six possible images of an ordered triple. -/
theorem enumeration : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∃ p : Perm, image p 0 = a ∧ image p 1 = b ∧ image p 2 = c ∧
      ∀ q : Perm, image q 0 = a → image q 1 = b → image q 2 = c → q = p := by decide

/-- The odd codes have an odd number of inversions in their image triple. -/
def odd (p : Perm) : Bool := p == 1 || p == 2 || p == 5

/-- Every code acts injectively on the three positions. -/
theorem image_injective : ∀ (p : Perm) (i j : Fin 3), image p i = image p j → i = j := by decide

/-- The sign bit agrees with the parity of the inversion count. -/
theorem odd_eq_inversions : ∀ p : Perm, odd p =
    (((decide (image p 0 > image p 1)).toNat + (decide (image p 0 > image p 2)).toNat +
      (decide (image p 1 > image p 2)).toNat) % 2 == 1) := by decide

/-- Left-compose with 021 (unswitched) or 201 (switched). -/
def step (b : Bool) (p : Perm) : Perm :=
  (if b then #[4, 5, 1, 0, 3, 2] else #[1, 0, 4, 5, 2, 3])[p.val]!

/-- Check composition in the image representation, including the direction of each map. -/
theorem image_step : ∀ (b : Bool) (p : Perm) (i : Fin 3),
    image (step b p) i = image (if b then 4 else 1) (image p i) := by decide

/-- Attainable forward transfers. The newest fiber is at the head of the word.
At a positive character the two strands take opposite local maps. -/
inductive Realizes : List Bool → Perm → Perm → Prop where
  /-- The empty word acts as the identity on both triples. -/
  | nil : Realizes [] 0 0
  /-- Choose either switch at the next fiber. -/
  | cons {w p q} (r : Realizes w p q) (a b : Bool) :
      Realizes (a :: w) (step b p) (step (b ^^ a) q)

/-- Parity of the number of positive characters. -/
def parity : List Bool → Bool
  | [] => false
  | a :: w => a ^^ parity w

private theorem stepParity : ∀ (a b : Bool) (p q : Perm),
    (odd (step b p) ^^ odd (step (b ^^ a) q)) = (a ^^ (odd p ^^ odd q)) := by decide

/-- Proposition 6.9. Every switch sequence has the prescribed sign product. -/
theorem parity_of_realizes {w p q} (h : Realizes w p q) : (odd p ^^ odd q) = parity w := by
  induction h with
  | nil => rfl
  | cons r a b ih => rw [stepParity, ih, parity]

-- The seventeen proper reachable subsets in the interval certificate, followed
-- by the two full parity classes. Bit 6*p+q encodes (p,q).
private abbrev State := Fin 19

private def contains (s : State) (p q : Perm) : Bool :=
  let masks : Array Nat := #[1, 268435584, 33555456, 34361851905, 1074823200, 8598327300,
    4295360520, 34630287489, 1108378656, 17784439362, 2302683408, 8631882756, 4563796104,
    26382766662, 6598043928, 18859262562, 36664535313, 41228331417, 27491145318]
  masks[s.val]!.testBit (6 * p.val + q.val)

private def advance (s : State) (a : Bool) : State :=
  (if a then #[2, 4, 6, 8, 10, 12, 9, 8, 14, 16, 13, 12, 15, 17, 13, 16, 18, 18, 17]
   else #[1, 3, 5, 7, 9, 11, 10, 7, 13, 15, 14, 11, 16, 18, 14, 15, 17, 17, 18])[s.val]!

private def run : List Bool → State
  | [] => 0
  | a :: w => advance (run w) a

private def undo (b : Bool) (p : Perm) : Perm :=
  if b then step true (step true p) else step false p

private theorem undo_spec : ∀ (b : Bool) (p : Perm), step b (undo b p) = p := by decide

private theorem initial : ∀ p q, contains 0 p q = true ↔ p = 0 ∧ q = 0 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem transition : ∀ (s : State) (a : Bool) (p q : Perm),
    contains (advance s a) p q = true ↔
    ∃ b : Bool, contains s (undo b p) (undo (b ^^ a) q) = true := by decide

private theorem realizes_of_contains {w p q} (h : contains (run w) p q = true) :
    Realizes w p q := by
  induction w generalizing p q with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (initial p q).mp h
    exact .nil
  | cons a w ih =>
    obtain ⟨b, hb⟩ := (transition (run w) a p q).mp h
    simpa only [undo_spec] using (ih hb).cons a b

-- Upper bounds on the number of positive characters before reaching a full state.
private def bound (s : State) : Nat :=
  (#[0, 0, 1, 0, 1, 1, 2, 0, 1, 3, 2, 1, 2, 3, 2, 3, 4, 0, 1] : Array Nat)[s.val]!

private theorem progress : ∀ (s : State) (a : Bool), (advance s a).val < 17 →
    s.val < 17 ∧ bound s + a.toNat ≤ bound (advance s a) := by decide

private theorem bound_run (w : List Bool) (h : (run w).val < 17) :
    w.count true ≤ bound (run w) := by
  induction w with
  | nil => decide
  | cons a w ih =>
    have ⟨hs, ha⟩ := progress (run w) a h
    have hb := ih hs
    cases a <;> simp_all [run] <;> omega

private theorem full_of_five {w : List Bool} (h : 5 ≤ w.count true) : 17 ≤ (run w).val := by
  have small : ∀ s : State, bound s ≤ 4 := by decide
  have := small (run w)
  by_cases hn : (run w).val < 17
  · have := bound_run w hn
    omega
  · omega

private theorem parity_advance : ∀ (s : State) (a : Bool),
    ((bound (advance s a)) % 2 == 1) = (a ^^ (bound s % 2 == 1)) := by decide

private theorem parity_run (w : List Bool) : (bound (run w) % 2 == 1) = parity w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [run, parity_advance, ih, parity]

private theorem full : ∀ (s : State) (p q : Perm), 17 ≤ s.val →
    (odd p ^^ odd q) = (bound s % 2 == 1) → contains s p q = true := by decide

/-- Lemma 6.10 in the forward convention. For any interval with at least five
positive characters, exactly the pairs of the prescribed parity are attainable. -/
theorem realizes_iff_of_five {w : List Bool} (h : 5 ≤ w.count true) (p q : Perm) :
    Realizes w p q ↔ (odd p ^^ odd q) = parity w := by
  refine ⟨parity_of_realizes, fun hp => realizes_of_contains ?_⟩
  exact full (run w) p q (full_of_five h) (hp.trans (parity_run w).symm)

end BipartiteKneser.Interval
