module

public import KneserConstruction.OrbitNames
public import KneserConstruction.FamilyZero

/-! # Lifting the zero-coordinate splice to the actual generic quadruples -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.Orbit

open Family Coordinates Fin.NatCast

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q} {ι : Type*}

private def zBlock (m : Multipliers p q) (k : Fin q) :=
  pairBlock (m := m) (Zero.Z m k) (Zero.Z m (k + 1))

/-- Slot number in the U,U⁻¹,V,V⁻¹ convention. -/
def rowSlot : Slot → Fin 4
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3

private theorem zero_path (F : Complete m ι) (k : Fin q) (ls : List (Fin q))
    (rows : ∀ Q ∈ Zero.path m k ls, HasRow F Q) :
    Across (onFrames F) (zBlock m k) (zBlock m (ls.getLastD k))
      (fun i => if ls.length % 2 = 0 then i else Splice.first i) ∧
    ∀ Q ∈ Zero.path m k ls, ∀ s, ∃ j, Reach (onFrames F) (Q.dom (inverse m) s)
      (zBlock m (ls.getLastD k) j) := by
  induction ls generalizing k with
  | nil => exact ⟨fun _ => .refl _, by simp [Zero.path]⟩
  | cons l ls ih =>
    have head : Across (onFrames F) (zBlock m k) (zBlock m l) Splice.first :=
      first_row (rows _ (.head _))
    obtain ⟨tail, drain⟩ := ih l (fun Q h => rows _ (.tail _ h))
    have path : Across (onFrames F) (zBlock m k) (zBlock m (ls.getLastD l))
        (fun i => if (ls.length + 1) % 2 = 0 then i else Splice.first i) := by
      intro i
      have h := (head i).trans (tail (Splice.first i))
      have inv : ∀ i, Splice.first (Splice.first i) = i := by decide
      by_cases he : ls.length % 2 = 0
      · simpa [he, show (ls.length + 1) % 2 ≠ 0 by omega] using h
      · simpa [he, show (ls.length + 1) % 2 = 0 by omega, inv] using h
    simp only [List.getLastD_cons, List.length_cons]
    refine ⟨path, ?_⟩
    intro Q hQ s
    rcases List.mem_cons.mp hQ with rfl | hQ
    · obtain ⟨u, v⟩ := s
      cases u <;> cases v
      · exact ⟨_, path 0⟩
      · exact ⟨_, path 1⟩
      · exact ⟨_, path 2⟩
      · exact ⟨_, path 3⟩
    · exact drain _ hQ s

/-- The seven concrete block names used by the machine-checked zero splice. -/
private def zPairs (m : Multipliers p q) (a b v : Fin q) : ℕ → Bool → Frame p q
  | 0, t => X m a (if t then -1 else 1)
  | 1, t => X m b (if t then -1 else 1)
  | 2, t => Zero.Z m (if t then 2 else 1)
  | 3, t => Zero.Z m (if t then 4 else 3)
  | 4, t => Zero.Z m (if t then 6 else 5)
  | 5, t => Zero.Z m (if t then 8 else 7)
  | _, t => Zero.Z m (if t then v + 1 else v)

private theorem concrete_rows (h2 : (2 : ZMod p) ≠ 0) (a b v : Fin q) (odd : Bool) :
    (Splice.zeroRows odd).map (instantiate (named m (zPairs m a b v))) =
      Zero.bridges m a b v ++ Zero.templates m odd := by
  cases odd <;>
    simp only [Splice.zeroRows, Zero.bridges, Zero.templates, Bool.false_eq_true, ite_false,
      ite_true, List.cons_append, List.nil_append, List.map_cons, List.map_nil, instantiate]
  all_goals
    norm_num [named, zPairs, Nat.testBit_eq_decide_div_mod_eq, Zero.Z, inverse_X' m h2]

private theorem symbolic_dom : ∀ (odd : Bool) (r : Splice.Row), r ∈ Splice.zeroRows odd →
    ∀ s, domAddress r s < 28 ∧ (odd = true ∨ domAddress r s / 4 ≠ 5) := by
  intro odd r hr
  cases odd <;> simp only [Splice.zeroRows, Bool.false_eq_true, ite_false, ite_true,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- All four paths at the modified exponent pair of fiber 1, together with a
path to the b-block from every source of every zero-coordinate row. -/
theorem zero_rows_paths (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0)
    {M j : ℕ} (hj : 4 ≤ j) (hM : j < M) (a b v : Fin q)
    (rows : ∀ Q ∈ Zero.rows m M j a b v, HasRow F Q) :
    Across (onFrames F) (fiber m a 1) (fiber m b 1) Splice.zeroExit ∧
    ∀ Q ∈ Zero.rows m M j a b v, ∀ s, ∃ i,
      Reach (onFrames F) (Q.dom (inverse m) s) (fiber m b 1 i) := by
  let odd := decide (M % 2 = 1)
  let pairs := zPairs m a b v
  let label := named m pairs
  let k : Fin q := Zero.start (Zero.cut odd)
  let ls := Zero.tail M j odd v
  have htail : ∀ Q ∈ Zero.path m k ls, HasRow F Q := fun Q h =>
    rows Q (List.mem_append_left _ (List.mem_append_right _ h))
  have last : ls.getLastD k = v := by simp [ls, Zero.tail]
  obtain ⟨tail, tailDrain⟩ := zero_path F k ls htail
  rw [last] at tail tailDrain
  have hc : Zero.cut odd < j := by cases odd <;> simp [Zero.cut] <;> omega
  have hjmem : j ∈ List.range' (Zero.cut odd + 1) (M - (Zero.cut odd + 1)) := by
    simp [List.mem_range'_1]; omega
  have len : ls.length = M - (Zero.cut odd + 1) := by
    simp [ls, Zero.tail, List.length_erase_of_mem hjmem]
    omega
  have oddLen : ls.length % 2 ≠ 0 := by
    rw [len]
    by_cases hm : M % 2 = 1 <;> simp [Zero.cut, odd, hm] <;> omega
  have special : Splice.Valid (onFrames F) label ((Splice.zeroRows odd).flatMap Splice.Row.edges) :=
    valid_splice_rows F label _ (named_mate pairs) fun r hr => by
      have h := List.mem_map_of_mem (f := instantiate label) hr
      rw [show (Splice.zeroRows odd).map (instantiate label) = _ from concrete_rows h2 a b v odd]
        at h
      rcases List.mem_append.mp h with h | h
      · exact rows _ (List.mem_append_right _ h)
      · exact rows _ (List.mem_append_left _ (List.mem_append_left _ h))
  have startEq : label ∘ Splice.addr (if odd then 5 else 4) = zBlock m k := by
    rw [show label = named m pairs from rfl, named_block]
    cases ho : odd <;> simp [pairs, zPairs, k, Zero.cut, ho, Zero.start, zBlock]
    all_goals congr 2
    · simpa only [show (5 : ℕ) + 1 = 6 by decide, Nat.cast_ofNat, Nat.cast_one] using
        (Nat.cast_add (R := Fin q) 5 1)
    · simpa only [show (7 : ℕ) + 1 = 8 by decide, Nat.cast_ofNat, Nat.cast_one] using
        (Nat.cast_add (R := Fin q) 7 1)
  have endEq : label ∘ Splice.addr 6 = zBlock m v := by
    rw [show label = named m pairs from rfl, named_block]
    rfl
  have long : Across (onFrames F) (label ∘ Splice.addr (if odd then 5 else 4))
      (label ∘ Splice.addr 6) Splice.first := by simpa only [startEq, endEq, oddLen, ite_false]
        using tail
  obtain ⟨cross, drain⟩ := Splice.zero odd special long
  have aEq : label ∘ Splice.addr 0 = fiber m a 1 := by
    rw [show label = named m pairs from rfl, named_block]; rfl
  have bEq : label ∘ Splice.addr 1 = fiber m b 1 := by
    rw [show label = named m pairs from rfl, named_block]; rfl
  rw [aEq, bEq] at cross
  have drain' (i : ℕ) (hi : i < 28) (live : odd = true ∨ i / 4 ≠ 5) :
      ∃ t, Reach (onFrames F) (label i) (fiber m b 1 t) := by
    obtain ⟨t, ht⟩ := drain ⟨i, hi⟩ live
    exact ⟨t, (congrFun bEq t) ▸ ht⟩
  refine ⟨cross, ?_⟩
  intro Q hQ s
  have h : Q ∈ Zero.bridges m a b v ++ Zero.templates m odd ∨ Q ∈ Zero.path m k ls := by
    simpa [Zero.rows, odd, k, ls, or_comm, or_left_comm, or_assoc] using hQ
  rcases h with h | h
  · rw [← concrete_rows h2] at h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    rw [named_dom]
    obtain ⟨hi, hLive⟩ := symbolic_dom odd r hr s
    exact drain' _ hi hLive
  · obtain ⟨i, hi⟩ := tailDrain _ h s
    have ha : Splice.addr 6 i < 28 ∧ Splice.addr 6 i / 4 ≠ 5 := by
      dsimp [Splice.addr]; omega
    obtain ⟨t, ht⟩ := drain' _ ha.1 (.inr ha.2)
    exact ⟨t, hi.trans ((congrFun endEq i) ▸ ht)⟩

end BipartiteKneser.Orbit
