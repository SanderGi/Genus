module

public import KneserConstruction.OrbitNames
public import KneserConstruction.FamilyTransRows

/-! # The four translation paths and exhaustion of their intermediate slots (Lemma 6.3) -/

@[expose] public section

namespace BipartiteKneser.Orbit

open Coordinates Family Family.Translations

variable {r : ℕ}

private theorem large (L : Layout r) : 5 < r := by have := L.upper; have := L.lower; omega

/-- Position in the cyclic list, allowing the terminal position r for the return to 1. -/
private def pos (L : Layout r) (n : ℕ) : Fin r :=
  (order L)[n % r]'(by rw [order_length]; exact Nat.mod_lt _ (by have := large L; omega))

private theorem pos_eq (L : Layout r) (n k : ℕ) :
    pos L n = pos L k ↔ n % r = k % r :=
  (order_nodup L).getElem_inj_iff

private theorem pos_next (L : Layout r) {n : ℕ} (hn : n < r) :
    next L (pos L n) = pos L (n + 1) := by
  unfold pos next
  rw [List.formPerm_apply_getElem _ (order_nodup L)]
  congr 1
  rw [Nat.mod_eq_of_lt hn, order_length]

private theorem pos_cuts (L : Layout r) :
    pos L 0 = first L ∧ pos L 1 = afterFirst L ∧ pos L 2 = second L ∧
      pos L 3 = afterSecond L ∧ pos L r = first L := by
  have h := large L
  simp [pos, Nat.mod_eq_of_lt (show 1 < r by omega), Nat.mod_eq_of_lt (show 2 < r by omega),
    Nat.mod_eq_of_lt (show 3 < r by omega), order, cuts]

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable {m : Multipliers p q} {ι : Type*}

private def trBlock (m : Multipliers p q) (i : Fin r) :=
  pairBlock (m := m) (U i) (V i)

/-- The six retained blocks of the finite translation splice. -/
private noncomputable def trPairs (m : Multipliers p q) (L : Layout r) (E : Fin q)
    (wa wb : ZMod p) :
    ℕ → Bool → Frame p q
  | 0,b => X m E (if b then -wa else wa)
  | 1,b => X m E (if b then -wb else wb)
  | 2,b => if b then V (first L) else U (first L)
  | 3,b => if b then V (afterFirst L) else U (afterFirst L)
  | 4,b => if b then V (second L) else U (second L)
  | _,b => if b then V (afterSecond L) else U (afterSecond L)

/-- Every translation row occurs in the chosen complete family. Only the parity of r
is used in tracing the cycle; the coordinate endpoints are otherwise arbitrary. -/
theorem translation_paths (F : Complete m ι) (L : Layout r) (E : Fin q) (wa wb : ZMod p)
    (h₂ : (2 : ZMod p) ≠ 0) (even : r % 2 = 0)
    (rows : ∀ i, HasRow F (Translations.row m L E wa wb i)) :
    Across (onFrames F) (fiber m E wa) (fiber m E wb) Splice.translationExit ∧
      ∀ (i : Fin r) (s : Fin 4), ∃ t, Reach (onFrames F)
        (pairBlock (m := m) (U i) (V i) s) (fiber m E wb t) := by
  obtain ⟨p0,p1,p2,p3,pr⟩ := pos_cuts L
  have hr := large L
  let layer (n : ℕ) := trBlock m (pos L n)
  have distinct {n k : ℕ} (hn : n < r) (hk : k < r) (h : n ≠ k) : pos L n ≠ pos L k := by
    simpa only [ne_eq, pos_eq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk] using h
  have ordinary (n : ℕ) (hn : n < r) (h0 : n ≠ 0) (h2 : n ≠ 2) (h3 : n ≠ 3) :
      Across (onFrames F) (layer n) (layer (n+1)) Splice.first := by
    have a := distinct hn (show 0 < r by omega) h0
    have b := distinct hn (show 2 < r by omega) h2
    have c := distinct hn (show 3 < r by omega) h3
    rw [p0] at a
    rw [p2] at b
    rw [p3] at c
    apply first_row
    simpa [Translations.row, a, b, c, pos_next L hn] using rows (some (pos L n))
  have reversed : Across (onFrames F) (layer 3) (layer 4) Splice.second := by
    have a := distinct (show 3 < r by omega) (show 0 < r by omega) (by decide)
    have b := distinct (show 3 < r by omega) (show 2 < r by omega) (by decide)
    rw [p0] at a
    rw [p2] at b
    apply second_row (inverse_twice m)
    simpa only [Translations.row, ite_eq_right a, ite_eq_right b, ite_eq_left p3,
      pos_next L (show 3 < r by omega)] using rows (some (pos L 3))
  have tailPath (n : ℕ) (lo : 4 ≤ n) (hi : n ≤ r) :
      Across (onFrames F) (layer n) (layer r)
        (fun i => if (r - n) % 2 = 0 then i else Splice.first i) := by
    have seg := Splice.first_chain (f := ⇑(onFrames F)) (fun t => layer (n+t)) (n := r - n)
      (fun t ht => ordinary (n+t) (by omega) (by omega) (by omega) (by omega))
    simpa only [Nat.add_zero, Nat.add_sub_of_le hi] using seg
  let pairs := trPairs m L E wa wb
  let chart := named m pairs
  have block (n : ℕ) : chart ∘ Splice.addr n =
      pairBlock (m := m) (pairs n false) (pairs n true) :=
    named_block pairs n
  have edges : Splice.Valid (onFrames F) chart
      (Splice.translationRows.flatMap Splice.Row.edges) := by
    apply valid_splice_rows F _ _ (named_mate pairs)
    intro R mem
    simp only [Splice.translationRows, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · change HasRow F ⟨U (second L), inverse m (V (second L)),
          inverse m (U (afterFirst L)), V (afterSecond L)⟩
      simpa [Translations.row, (first_ne_second L).symm] using rows (some (second L))
    · change HasRow F ⟨U (first L), X m E (-wa), U (afterSecond L), inverse m (X m E wb)⟩
      simpa [Translations.row, inverse_X' m h₂] using rows (some (first L))
    · change HasRow F ⟨V (first L), X m E wa, inverse m (V (afterFirst L)),
          inverse m (X m E (-wb))⟩
      simpa [Translations.row, inverse_X' m h₂] using rows none
  have short : Across (onFrames F) (chart ∘ Splice.addr 3) (chart ∘ Splice.addr 4)
      Splice.first := by
    rw [block, block]
    change Across _ (trBlock m (afterFirst L)) (trBlock m (second L)) _
    simpa only [layer, p1, p2] using ordinary 1 (by omega) (by decide) (by decide) (by decide)
  have long : Across (onFrames F) (chart ∘ Splice.addr 5) (chart ∘ Splice.addr 2)
      Splice.second := by
    rw [block, block]
    change Across _ (trBlock m (afterSecond L)) (trBlock m (first L)) _
    have he : (r - 4) % 2 = 0 := by omega
    intro i
    have path := (reversed i).trans (tailPath 4 (by decide) (by omega) _)
    simpa only [ite_eq_left he, layer, p3, pr] using path
  obtain ⟨ports, drains⟩ := Splice.translation edges short long
  have exitEq : chart ∘ Splice.addr 1 = fiber m E wb := block 1
  constructor
  · simpa only [exitEq, show chart ∘ Splice.addr 0 = fiber m E wa from block 0] using ports
  · have drain (b : ℕ) (hb : b < 6) (s : Fin 4) :
        ∃ t, Reach (onFrames F) (pairBlock (m := m) (pairs b false) (pairs b true) s)
          (fiber m E wb t) := by
      rw [← block]
      have hs := s.isLt
      obtain ⟨t,ht⟩ := drains ⟨Splice.addr b s, by unfold Splice.addr; omega⟩
      exact ⟨t, (congrFun exitEq t) ▸ ht⟩
    intro i s
    obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp (mem_order L i)
    rw [order_length] at hn
    have pi : pos L n = i := by simpa [pos, Nat.mod_eq_of_lt hn] using eq
    rw [← pi]
    by_cases low : n < 4
    · interval_cases n
      · rw [p0]; simpa [pairs, trPairs] using drain 2 (by decide) s
      · rw [p1]; simpa [pairs, trPairs] using drain 3 (by decide) s
      · rw [p2]; simpa [pairs, trPairs] using drain 4 (by decide) s
      · rw [p3]; simpa [pairs, trPairs] using drain 5 (by decide) s
    · have path := tailPath n (by omega) hn.le s
      obtain ⟨t,ht⟩ := drain 2 (by decide) (if (r-n)%2 = 0 then s else Splice.first s)
      exact ⟨t, path.trans (by simpa [pairs, trPairs, layer, pr, trBlock] using ht)⟩

end BipartiteKneser.Orbit
