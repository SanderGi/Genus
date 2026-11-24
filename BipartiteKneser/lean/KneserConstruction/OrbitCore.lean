module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Lifting cycles across omitted vertices -/

@[expose] public section

namespace BipartiteKneser.Orbit

variable {α β γ : Type*}

/-- Forward reachability, including a path of length zero at a shared port. -/
def Reach (f : α → α) (x y : α) : Prop := ∃ n : ℕ, f^[n] x = y

/-- Every ordered pair of local labels lies on one forward orbit. -/
def OneCycle (f : α → α) : Prop := ∀ x y, Reach f x y

namespace Reach

variable {f : α → α} {x y z : α}

/-- Zero iterations give a path from each label to itself. -/
@[refl] theorem refl (x : α) : Reach f x x := ⟨0, rfl⟩

/-- A single assignment of the rotation is a forward path. -/
theorem step (h : f x = y) : Reach f x y := ⟨1, h⟩

/-- Concatenate two forward paths at their common label. -/
@[trans] theorem trans (h : Reach f x y) (k : Reach f y z) : Reach f x z := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := k
  exact ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩

/-- On a finite permutation cycle, continuing forward from the endpoint returns to the starting
label. -/
theorem reverse [Finite α] {f : Equiv.Perm α} (h : Reach f x y) : Reach f y x := by
  obtain ⟨n, hn⟩ := h
  have hc : f.SameCycle x y := ⟨n, by simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hn⟩
  simpa only [Reach, Equiv.Perm.coe_pow] using hc.symm.exists_nat_pow_eq

end Reach

/-- A simulation of every compressed edge by a path of the original rotation. -/
def Routes (f : α → α) (g : β → β) (port : β → α) : Prop :=
  ∀ b, Reach f (port b) (port (g b))

/-- Lift a path of the compressed rotation by following the route for each edge. -/
theorem Routes.lift {f : α → α} {g : β → β} {port : β → α} (r : Routes f g port)
    {x y : β} (h : Reach g x y) : Reach f (port x) (port y) := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact .refl _
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (r _)

/-- Every cycle meets the retained labels. -/
def Drains (f : α → α) (port : β → α) : Prop := ∀ a, ∃ b, Reach f a (port b)

/-- A cycle on the retained labels lifts if every omitted label reaches a retained one. -/
theorem oneCycle_of_contraction [Finite α] {f : Equiv.Perm α} {g : β → β} {port : β → α}
    (routes : Routes f g port) (hits : Drains f port) (cycle : OneCycle g) : OneCycle f := by
  intro x y
  obtain ⟨a, ha⟩ := hits x
  obtain ⟨b, hb⟩ := hits y
  exact (ha.trans (routes.lift (cycle a b))).trans hb.reverse

/-- A chain of layers, with a possibly different state map at each step. -/
def Across (f : α → α) (A B : β → α) (π : β → β) : Prop :=
  ∀ i, Reach f (A i) (B (π i))

/-- Compose the slot maps of two consecutive layers by concatenating their paths. -/
theorem Across.comp {f : α → α} {A B C : β → α} {s t : β → β}
    (a : Across f A B s) (b : Across f B C t) : Across f A C (t ∘ s) :=
  fun i => (a i).trans (b _)

/-- Following any suffix of an indexed chain yields an exit, including at its last layer. -/
theorem chain_exit {f : α → α} (layer : ℕ → β → α) {n : ℕ}
    (advance : ∀ k < n, ∀ i, ∃ j, Reach f (layer k i) (layer (k + 1) j))
    {k : ℕ} (hk : k ≤ n) (i : β) : ∃ j, Reach f (layer k i) (layer n j) := by
  induction n generalizing k i with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact ⟨_, .refl _⟩
  | succ n ih =>
    by_cases he : k = n + 1
    · subst k; exact ⟨_, .refl _⟩
    · obtain ⟨j, hj⟩ := ih (fun l hl => advance l (by omega)) (by omega : k ≤ n) i
      obtain ⟨z, hz⟩ := advance n (by omega) j
      exact ⟨z, hj.trans hz⟩

end BipartiteKneser.Orbit
