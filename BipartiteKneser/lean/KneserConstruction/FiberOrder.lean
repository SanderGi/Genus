import KneserConstruction.FamilyChains
import KneserConstruction.CoordinateResidues

/-! # Ordering the present exponent pairs of a positive coordinate fiber -/

namespace BipartiteKneser.Family.FiberOrder

open Coordinates

variable {p q r : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

abbrev Exponent (q : ℕ) [NeZero q] := {k : Fin q // k ≠ 0}

variable (size : q = 2 * r + 1)

/-- Positive representative for an exponent pair. -/
noncomputable def pos (i : Fin r) : Exponent q := signedResidueEquiv size (i, false)

/-- Forget the orientation of an exponent. -/
noncomputable def key (k : Exponent q) : Fin r := ((signedResidueEquiv size).symm k).1

@[simp] theorem key_pos (i : Fin r) : key size (pos size i) = i := by simp [key, pos]

theorem val_pos (i : Fin r) : (pos size i).val = (Fin.ofNat q (i.val + 1)) :=
  signedResidueEquiv_pos size i

theorem signed (k : Exponent q) : k.val = (pos size (key size k)).val ∨
    k.val = -(pos size (key size k)).val := by
  obtain ⟨⟨i, b⟩, rfl⟩ := (signedResidueEquiv size).surjective k
  cases b <;> simp [pos, key]

theorem key_eq_iff (k l : Exponent q) :
    key size k = key size l ↔ k.val = l.val ∨ k.val = -l.val := by
  constructor
  · intro h
    rcases signed size k with hk | hk <;> rcases signed size l with hl | hl <;> grind
  · rintro (h | h)
    · exact congrArg (key size) (Subtype.ext h)
    · obtain ⟨⟨i, b⟩, rfl⟩ := (signedResidueEquiv size).surjective l
      have same : k = signedResidueEquiv size (i, !b) := by
        apply Subtype.ext
        cases b <;> simpa using h
      rw [same]
      simp [key]


variable (m : Multipliers p q) (w : ZMod p)

/-- All present positive representatives, in increasing order. -/
noncomputable def present : List (Fin r) :=
  (List.finRange r).filter fun i => separated m.power (X m (pos size i).val w)

/-- Insert the specified oriented prefix and last pair, filling the middle with
the unused positive representatives. -/
noncomputable def middle (front : List (Exponent q)) (last : Exponent q) : List (Exponent q) :=
  ((present size m w).filter fun i => i ∉ (front ++ [last]).map (key size)).map (pos size)

noncomputable def order (front : List (Exponent q)) (last : Exponent q) : List (Exponent q) :=
  front ++ middle size m w front last ++ [last]

theorem perm_keys (front : List (Exponent q)) (last : Exponent q)
    (unique : ((front ++ [last]).map (key size)).Nodup)
    (allowed : ∀ k ∈ front ++ [last], key size k ∈ present size m w) :
    ((order size m w front last).map (key size)).Perm (present size m w) := by
  let picked := (front ++ [last]).map (key size)
  let rest := (present size m w).filter fun i => i ∉ picked
  have hp : (present size m w).Nodup := (List.nodup_finRange r).filter _
  have perm : (picked ++ rest).Perm (present size m w) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨unique, hp.filter _, ?_⟩) hp).mpr
    · intro i
      simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
      have h : i ∈ picked → i ∈ present size m w := by
        rintro hi
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
        exact allowed k hk
      tauto
    · intro i hi j hj he
      exact (List.mem_filter.mp hj).2 |> of_decide_eq_true |> fun hn => hn (he ▸ hi)
  have mid : (middle size m w front last).map (key size) = rest := by
    simp [middle, rest, picked, Function.comp_def]
  simp only [order, List.map_append, List.map_singleton, mid]
  apply List.Perm.trans _ perm
  simp only [picked, List.map_append, List.map_singleton]
  simpa [List.append_assoc] using
    (List.perm_append_comm (l₁ := rest) (l₂ := [key size last])).append_left (front.map (key size))

theorem inventory (h₂ : (2 : ZMod p) ≠ 0) (front : List (Exponent q)) (last : Exponent q)
    (unique : ((front ++ [last]).map (key size)).Nodup)
    (allowed : ∀ k ∈ front ++ [last], key size k ∈ present size m w) :
    ((order size m w front last).map fun k => quartet m k.val w).sum =
    ∑ i : Fin r, if separated m.power (X m (pos size i).val w) then
      quartet m (pos size i).val w else 0 := by
  let Q (i : Fin r) := quartet m (pos size i).val w
  have eq (k : Exponent q) : quartet m k.val w = Q (key size k) := by
    rcases signed size k with h | h
    · rw [h]
    · exact (congrArg (fun t => quartet m t w) h).trans (quartet_neg m h₂ _ w)
  simp_rw [eq]
  simp only [key_pos]
  change (List.map (Q ∘ key size) _).sum = _
  rw [← List.map_map, ((perm_keys size m w front last unique allowed).map Q).sum_eq]
  unfold present
  let keep (i : Fin r) := separated m.power (X m (pos size i).val w)
  have filter_sum (xs : List (Fin r)) : ((xs.filter keep).map Q).sum =
      (xs.map fun i => if keep i then Q i else 0).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih => cases h : keep i <;> simp [h, ih]
  rw [filter_sum]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

end BipartiteKneser.Family.FiberOrder
