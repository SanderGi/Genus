import KneserConstruction.FamilyTransRows
import KneserConstruction.CoordinateResidues

/-! # Exact coverage of the exponent-zero slice by the signed translation slots -/

namespace BipartiteKneser.Family.Translations

open Coordinates

variable {p q r : ℕ}

/-- Least nonnegative residue of a signed translation slot. -/
def residue (p : ℕ) (i : Fin r) (s : Slot) : ℕ :=
  let a := (if s.1 then r else 0) + i.val + 2
  if s.2 then p - a else a

private theorem residue_bounds (hp : p = 4 * r + 3) (i : Fin r) (s : Slot) :
    2 ≤ residue p i s ∧ residue p i s + 1 < p := by
  obtain ⟨b,t⟩ := s
  have := i.isLt
  cases b <;> cases t <;> simp [residue] <;> omega

private theorem residue_inj (hp : p = 4 * r + 3) :
    Function.Injective (fun x : Fin r × Slot => residue p x.1 x.2) := by
  rintro ⟨i,b,t⟩ ⟨j,c,u⟩ e
  have hi := i.isLt
  have hj := j.isLt
  subst p
  cases b <;> cases c <;> cases t <;> cases u <;> simp [residue] at e
  all_goals simp [Fin.ext_iff]; omega

private theorem residue_onto (hp : p = 4 * r + 3) {n : ℕ} (lo : 2 ≤ n) (hi : n + 1 < p) :
    ∃ i : Fin r × Slot, residue p i.1 i.2 = n := by
  by_cases a : n ≤ r + 1
  · exact ⟨(⟨n-2, by omega⟩,false,false), by simp [residue]; omega⟩
  by_cases b : n ≤ 2*r + 1
  · exact ⟨(⟨n-r-2, by omega⟩,true,false), by simp [residue]; omega⟩
  by_cases c : p-n ≤ r + 1
  · exact ⟨(⟨p-n-2, by omega⟩,false,true), by simp [residue]; omega⟩
  exact ⟨(⟨p-n-r-2, by omega⟩,true,true), by simp [residue]; omega⟩

variable [NeZero p] [NeZero q] [Fact p.Prime] (m : Multipliers p q)

theorem label_some (hp : p = 4 * r + 3) (k : Fin q) (w : ZMod p) (i : Fin r) (s : Slot) :
    label m k w (some i,s) = T ((residue p i s : ℕ) : ZMod p) := by
  obtain ⟨b,t⟩ := s
  have hi := i.isLt
  have h₁ : i.val + 2 ≤ p := by omega
  have h₂ : r + i.val + 2 ≤ p := by omega
  cases b <;> cases t <;>
    simp [label, U, V, residue, inverse_T, Nat.cast_sub h₁, Nat.cast_sub h₂]

private theorem residue_ok {n : ℕ} (lo : 2 ≤ n) (hi : n + 1 < p) :
    separated m.power (T (q := q) (n : ZMod p)) = true := by
  rw [separated_T_iff]
  have hn := ZMod.val_natCast_of_lt (show n < p by omega)
  have h1 := ZMod.val_natCast_of_lt (show 1 < p by omega)
  have hn1 := ZMod.val_natCast_of_lt hi
  constructor
  · intro e
    rw [e, ZMod.val_zero] at hn
    omega
  constructor
  · intro e
    simp only [Nat.cast_one] at h1
    rw [e, h1] at hn
    omega
  · intro e
    rw [Nat.cast_add, Nat.cast_one, e, neg_add_cancel, ZMod.val_zero] at hn1
    omega

/-- Enumeration of precisely the separated translation frames, in the local slot convention. -/
noncomputable def translationEquiv (hp : p = 4 * r + 3) :
    (Fin r × Slot) ≃ {x : Label m // x.val.2 = 0} := by
  let f (x : Fin r × Slot) : {z : Label m // z.val.2 = 0} :=
    ⟨⟨T ((residue p x.1 x.2 : ℕ) : ZMod p),
      residue_ok m (residue_bounds hp x.1 x.2).1 (residue_bounds hp x.1 x.2).2⟩, rfl⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y e
    have h := congrArg (fun z : {z : Label m // z.val.2 = 0} =>
      (ZMod.finEquiv p z.val.val.1).val) e
    have lt (i : Fin r × Slot) : residue p i.1 i.2 < p := by
      have := residue_bounds hp i.1 i.2
      omega
    simp only [f, T, RingEquiv.apply_symm_apply, ZMod.val_natCast_of_lt (lt x),
      ZMod.val_natCast_of_lt (lt y)] at h
    exact residue_inj hp h
  · rintro ⟨⟨⟨a,k⟩, ok⟩, hk⟩
    change k = 0 at hk
    subst k
    let c := ZMod.finEquiv p a
    have hc : T (q := q) c = (a,0) := by simp [T, c]
    rw [← hc, separated_T_iff] at ok
    have lt := c.val_lt
    have cast := ZMod.natCast_zmod_val c
    have lo : 2 ≤ c.val := by
      by_contra! h
      rcases (show c.val = 0 ∨ c.val = 1 by omega) with e | e <;> rw [e] at cast <;> simp_all
    have hi : c.val + 1 < p := by
      by_contra! h
      have eq : c.val + 1 = p := by omega
      have he := congrArg (Nat.cast : ℕ → ZMod p) eq
      rw [Nat.cast_add, Nat.cast_one, cast, ZMod.natCast_self] at he
      exact ok.2.2 (eq_neg_of_add_eq_zero_left he)
    obtain ⟨i, hi'⟩ := residue_onto hp lo hi
    exact ⟨i, Subtype.ext (Subtype.ext (by simpa only [f, hi', cast] using hc))⟩

theorem translationEquiv_val (hp : p = 4 * r + 3) (k : Fin q) (w : ZMod p)
    (i : Fin r) (s : Slot) :
    ((translationEquiv m hp (i,s)).val).val = label m k w (some i,s) :=
  (label_some m hp k w i s).symm

end BipartiteKneser.Family.Translations
