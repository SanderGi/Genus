/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import HoG.Cut
public import HoG.Boundary

/-! # Optimizing one vertex while fixing every turn away from it -/

@[expose] public section

namespace HoG.Excursions

open Equiv Equiv.Perm MultiGenus.Surgery HoG.Cut

variable {A B I J : Type*}

/-- Rearranging the four dart sets places all root darts together. -/
abbrev regroup (A B I J : Type*) := sumSumSumComm A B I J

/-- A single root rotation, with an independent exterior rotation on each piece. -/
def join (r : Perm (A ⊕ B)) (s : Perm I) (t : Perm J) : Perm ((A ⊕ I) ⊕ B ⊕ J) :=
  (regroup A B I J).permCongr (r.sumCongr (s.sumCongr t))

private def inclusion (A I : Type*) : A ↪ A ⊕ I := ⟨Sum.inl, Sum.inl_injective⟩

private theorem rewire_side (r : Perm A) (s : Perm I) (v : Perm (A ⊕ I)) :
    Rewire Sum.inl ((1 : Perm A).sumCongr s * v) (r.sumCongr s * v) r := by
  constructor
  · intro x a h
    change ((1 : Perm A).sumCongr s) (v x) = _ at h
    change (r.sumCongr s) (v x) = _
    cases eq : v x with
    | inl b => rw [eq] at h; exact congrArg (fun z => Sum.inl (r z)) (Sum.inl.inj h)
    | inr j => rw [eq] at h; cases h
  · intro x h
    change (r.sumCongr s) (v x) = ((1 : Perm A).sumCongr s) (v x)
    cases eq : v x with
    | inl b => exact (h b (by simp [Perm.mul_apply, eq])).elim
    | inr j => rfl

private theorem rewire_join (r : Perm (A ⊕ B)) (s : Perm I) (t : Perm J)
    (v : Perm (A ⊕ I)) (w : Perm (B ⊕ J)) :
    Rewire (Sum.map Sum.inl Sum.inl)
      (((1 : Perm A).sumCongr s * v).sumCongr ((1 : Perm B).sumCongr t * w))
      (join r s t * v.sumCongr w) r := by
  let e := regroup A B I J
  let base := ((1 : Perm A).sumCongr s * v).sumCongr ((1 : Perm B).sumCongr t * w)
  let gate := e.permCongr (r.sumCongr (1 : Perm (I ⊕ J)))
  have canon (z : A ⊕ B) : Sum.map (Sum.inl : A → A ⊕ I) (Sum.inl : B → B ⊕ J) z =
      e (.inl z) := by cases z <;> rfl
  have step (x) : (join r s t * v.sumCongr w) x = gate (base x) := by
    rcases x with x | x
    · change (join r s t) (.inl (v x)) = gate (.inl (((1 : Perm A).sumCongr s) (v x)))
      cases v x <;> rfl
    · change (join r s t) (.inr (w x)) = gate (.inr (((1 : Perm B).sumCongr t) (w x)))
      cases w x <;> rfl
  constructor
  · intro x b h
    change base x = _ at h
    rw [step, h, canon, canon]
    simp [gate, Equiv.permCongr_apply]
  · intro x h
    rw [step]
    change gate (base x) = base x
    obtain ⟨z, hz⟩ := e.surjective (base x)
    rcases z with b | j
    · exact (h b (hz.symm.trans (canon b).symm)).elim
    · rw [← hz]
      simp [gate, Equiv.permCongr_apply]

variable [Finite A] [Finite B] [Finite I] [Finite J] [Nonempty A] [Nonempty B]

/-- With all other rotations fixed, optimal choices at the two separate roots produce exactly
one more face in total than an optimal cyclic ordering at their identified root. The three
bounds range over all cyclic orders, including orders interleaving darts from both pieces. -/
theorem fixed_exterior (s : Perm I) (t : Perm J) (v : Perm (A ⊕ I)) (w : Perm (B ⊕ J)) :
    ∃ (a : Perm A) (b : Perm B) (c : Perm (A ⊕ B)),
      (∀ x y, a.SameCycle x y) ∧ (∀ x y, b.SameCycle x y) ∧ (∀ x y, c.SameCycle x y) ∧
      (∀ r : Perm A, (∀ x y, r.SameCycle x y) →
        countCycles (r.sumCongr s * v) ≤ countCycles (a.sumCongr s * v)) ∧
      (∀ r : Perm B, (∀ x y, r.SameCycle x y) →
        countCycles (r.sumCongr t * w) ≤ countCycles (b.sumCongr t * w)) ∧
      (∀ r : Perm (A ⊕ B), (∀ x y, r.SameCycle x y) →
        countCycles (join r s t * v.sumCongr w) ≤ countCycles (join c s t * v.sumCongr w)) ∧
      countCycles (join c s t * v.sumCongr w) + 1 =
        countCycles (a.sumCongr s * v) + countCycles (b.sumCongr t * w) := by
  classical
  let l := firstReturn ((1 : Perm A).sumCongr s * v) (inclusion A I)
  let h := firstReturn ((1 : Perm B).sumCongr t * w) (inclusion B J)
  have left (r : Perm A) := l.count r (rewire_side r s v)
  have right (r : Perm B) := h.count r (rewire_side r t w)
  have both (r : Perm (A ⊕ B)) : countCycles (join r s t * v.sumCongr w) =
      countCycles (r * l.ret.sumCongr h.ret) + (countCycles l.inner + countCycles h.inner) :=
    ((l.sum h).count r (rewire_join r s t v w)).trans
      (congrArg (_ + ·) (countCycles_sum l.inner h.inner))
  obtain ⟨a, ha, ea⟩ := Boundary.attains l.ret
  obtain ⟨b, hb, eb⟩ := Boundary.attains h.ret
  obtain ⟨c, hc, ec⟩ := Boundary.attains (l.ret.sumCongr h.ret)
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [left, left]
    have := Boundary.upper l.ret r hr
    omega
  · intro r hr
    rw [right, right]
    have := Boundary.upper h.ret r hr
    omega
  · intro r hr
    rw [both, both]
    have := Boundary.upper (l.ret.sumCongr h.ret) r hr
    omega
  · rw [both, left, right, countCycles_sum, Nat.card_sum] at *
    omega

end HoG.Excursions
