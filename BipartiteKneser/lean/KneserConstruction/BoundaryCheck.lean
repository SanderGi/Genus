import KneserConstruction.BoundaryModel

/-! The Section 7 certificate checker and its bounded quantifier. -/

namespace BipartiteKneser.Boundary

def maskOf (v : Nat) := v / 64
def plusOf (v : Nat) : Interval.Perm := Fin.ofNat 6 ((v / 8) % 8)
def minusOf (v : Nat) : Interval.Perm := Fin.ofNat 6 (v % 8)

/-- Require the first hit of zero after exactly the given number of further steps. -/
def firstHit {n : Nat} [NeZero n] (f : Fin n → Fin n) : Nat → Fin n → Bool
  | 0, x => x == 0
  | k + 1, x => x != 0 && firstHit f k (f x)

/-- Match the current numeral before the next step to keep kernel reductions small. -/
private def walk (f : Nat → Nat) : Nat → Nat → Bool
  | 0, x => x == 0
  | _+1, 0 => false
  | k + 1, x + 1 => walk f k (f (x + 1))

private theorem walk_eq {n : Nat} [NeZero n] (f : Fin n → Fin n) (k : Nat) (x : Fin n) :
    walk (fun t => (f (Fin.ofNat n t)).val) k x.val = firstHit f k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv⟩ := x
    cases v with
    | zero => simp [walk, firstHit]
    | succ v =>
      have h : (⟨v + 1,hv⟩ : Fin n) ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this
      simp only [walk, firstHit, bne_iff_ne.mpr h, Bool.true_and, ← ih]
      have e : Fin.ofNat n (v + 1) = ⟨v + 1,hv⟩ := Fin.ext (Nat.mod_eq_of_lt hv)
      rw [e]

def check (c : Case) (chars : Pattern c) (v : Nat) : Bool :=
  let mask := maskOf v
  let p := plusOf v
  let r := minusOf v
  let f := step c chars mask p r
  (choices c).contains mask &&
    ((Interval.odd p ^^ Interval.odd r) == positiveParity c chars) &&
    walk (fun t => (f (Fin.ofNat _ t)).val) (size c - 1) (f 0).val

theorem check_sound {c : Case} {chars : Pattern c} {v : Nat} (h : check c chars v = true) :
    maskOf v ∈ choices c ∧ (Interval.odd (plusOf v) ^^ Interval.odd (minusOf v)) =
      positiveParity c chars ∧ firstHit (step c chars (maskOf v) (plusOf v) (minusOf v))
        (size c - 1) (step c chars (maskOf v) (plusOf v) (minusOf v) 0) = true := by
  simpa only [check, walk_eq, Bool.and_eq_true_iff, List.contains_iff_mem, beq_iff_eq,
    and_assoc] using h

private def strictCheck (c : Case) (chars : Pattern c) (v : Nat) : Bool :=
  match v with
  | 0 => check c chars 0
  | k + 1 => check c chars (k + 1)

private theorem strictCheck_eq (c : Case) (chars : Pattern c) (v : Nat) :
    strictCheck c chars v = check c chars v := by cases v <;> rfl

/-- A block stores one 16-bit proposal for each consecutive sign pattern. -/
def checkBlock (c : Case) (start data : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => strictCheck c (Fin.ofNat _ (start + k)) ((data >>> (16 * k)) % 65536) &&
      checkBlock c start data k

def Covered (c : Case) (start len : Nat) : Prop :=
  ∀ j : Fin len, ∃ v, check c (Fin.ofNat _ (start + j.val)) v = true

theorem covered_of_check (c : Case) (start data len : Nat)
    (h : checkBlock c start data len = true) : Covered c start len := by
  induction len with
  | zero => intro j; exact Fin.elim0 j
  | succ k ih =>
    obtain ⟨last, prev⟩ := Bool.and_eq_true_iff.mp h
    intro j
    by_cases hj : j.val = k
    · rw [hj]
      exact ⟨_, (strictCheck_eq ..).symm.trans last⟩
    · exact ih prev ⟨j.val, by have := j.isLt; omega⟩

theorem covered_append {c : Case} {start n m : Nat} (a : Covered c start n)
    (b : Covered c (start + n) m) : Covered c start (n + m) := by
  intro j
  by_cases hj : j.val < n
  · exact a ⟨j.val, hj⟩
  · have he : start + n + (j.val - n) = start + j.val := by omega
    simpa only [he] using b ⟨j.val - n, by have := j.isLt; omega⟩

end BipartiteKneser.Boundary
