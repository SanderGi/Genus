import KneserConstruction.ReductionInterval

/-! # Lifting the compressed boundary edges and draining every omitted state -/

namespace BipartiteKneser.Reduction
open Boundary Orbit

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]
variable {m : Multipliers p q} {ι : Type*} {F : Family.Complete m ι} {c : Case}
variable {N E K : Fin q} {χ : ℕ → Bool}

/-- The first affine frame corresponding to a retained boundary label. -/
noncomputable def retained (c : Case) (m : Multipliers p q) (N E : Fin q) (x : Boundary.Label c) :=
  firstFrame c m N E (decode c q x)

private theorem decode_low (c : Case) {q : ℕ} (hq : 65 ≤ q) (x : Boundary.Label c)
    (hx : x.val < 4 * count c) :
    decode c q x = slotPoint (outsideNat c q (x.val / 4)) (x.val % 4) := by
  have bit (j : ℕ) (hj : j < 2) : (x.val % 4).testBit j = x.val.testBit j := by
    simpa only [Nat.reducePow, hj, decide_true, Bool.true_and] using
      Nat.testBit_mod_two_pow x.val 2 j
  simp [decode, hx, slotPoint, outside_cast c hq, bit 0 (by decide), bit 1 (by decide)]

private theorem outside_hit (c : Case) {q w : ℕ} (hq : 65 ≤ q) (hw : 1 ≤ w) (hwq : w < q)
    (outside : w < start c ∨ stop c q ≤ w) (j : Fin 4) :
    ∃ x : Boundary.Label c, decode c q x = slotPoint w j := by
  have sz := sizes c
  rw [stop_eq c hq] at outside
  have ind : ∃ i, i < count c ∧ outsideNat c q i = w := by
    rcases outside with h | h
    · refine ⟨w - 1, by unfold start at h; omega, ?_⟩
      unfold outsideNat start at *
      split <;> omega
    · refine ⟨count c - (q - w), by omega, ?_⟩
      unfold outsideNat; split <;> omega
  obtain ⟨i, hi, rfl⟩ := ind
  have hj := j.isLt
  let x : Boundary.Label c := ⟨4 * i + j.val, by unfold size; omega⟩
  have hx : x.val < 4 * count c := by dsimp [x]; omega
  refine ⟨x, ?_⟩
  rw [decode_low c hq x hx]
  dsimp [x]
  rw [show (4 * i + j.val) / 4 = i by omega, show (4 * i + j.val) % 4 = j.val by omega]

private theorem entry_cases (j : Fin 6) : ∃ minus i, addr minus i = j.val := by
  fin_cases j
  · exact ⟨false, 0, rfl⟩
  · exact ⟨false, 1, rfl⟩
  · exact ⟨false, 2, rfl⟩
  · exact ⟨true, 0, rfl⟩
  · exact ⟨true, 1, rfl⟩
  · exact ⟨true, 2, rfl⟩

private theorem transfer_addr (a b : Interval.Perm) (minus : Bool) (i : Fin 3) :
    transferIndex a b (addr minus i) =
      addr minus (Interval.image (if minus then b else a) i) := by
  cases minus <;> fin_cases i <;> rfl

theorem routes {mask : ℕ} {s : ℕ → Bool} {a b : Interval.Perm}
    (h : LocalPaths c F N E K χ (switches c q mask s)) (hq : 65 ≤ q)
    (ha : forward (fun k => χ (start c + k)) s false (length c q) = a)
    (hb : forward (fun k => χ (start c + k)) s true (length c q) = b) :
    Routes (onFrames F) (step c (pattern c q χ) mask a b) (retained c m N E) := by
  intro x
  unfold retained
  rw [normalize_step c q (by exact_mod_cast hq)]
  by_cases hx : x.val < 4 * count c
  · let i := x.val / 4
    let j := x.val % 4
    have hi : i < count c := by dsimp [i]; omega
    obtain ⟨hw, hwq, h1⟩ := outside_bounds c hq hi
    have path := h.first_next (w := outsideNat c q i) (j := j) hw hwq (Nat.mod_lt _ (by decide))
    have hs : ∀ z t, lastSlot (outsideNat c q i - 1) j z t = lastSlot i j z t := by
      intro z t
      by_cases he : i = 0
      · rw [h1.mpr he, he]
      · have hne : outsideNat c q i - 1 ≠ 0 := by omega
        simp [lastSlot, he, hne]
    rw [hs, switches_outside c hq hi, ← pattern_bit c q χ hi] at path
    rw [decode_low c hq x hx]
    simpa only [coordinateStep, hx, ite_true, outside_cast c hq, i, j] using path
  · let j : Fin 6 := ⟨x.val - 4 * count c, by have := x.isLt; unfold size at this; omega⟩
    obtain ⟨minus, i, hj⟩ := entry_cases j
    have path := interval_paths (χ := fun k => χ (start c + k)) (s := s) (n := length c q)
      (f := ⇑(onFrames F)) (layer c m N E)
      (fun k hk minus => by
        simpa only [switches_inside c q mask s hk] using interval_step h hq hk minus)
      minus i
    have code : forward (fun k => χ (start c + k)) s minus (length c q) = if minus then b else a :=
      by cases minus <;> assumption
    have exit : ((start c + length c q : ℕ) : ℤ) = (q : ℤ) - (count c - leftCount c : ℕ) := by
      have sz := sizes c
      rw [← stop, stop_eq c hq, Nat.cast_sub (by omega)]
    change addr minus i = x.val - 4 * count c at hj
    rw [code] at path
    simp only [layer, Nat.add_zero, exit] at path
    simpa only [decode, coordinateStep, hx, ite_false, ← hj, transfer_addr, start] using path

private theorem exit_point {c : Case} {q : ℕ} (hq : 65 ≤ q) (minus : Bool) (i : Fin 3) :
    ∃ x : Boundary.Label c, decode c q x = port (stop c q) (addr minus i) := by
  have st := stop_eq c hq
  have sz : leftCount c + 2 < count c := by cases c <;> decide
  have sz' := sizes c
  have legal (u : ℕ) (hu : u ≤ 1) (j : Fin 4) :
      ∃ x : Boundary.Label c, decode c q x = slotPoint ((stop c q : ℤ) + u) j := by
    have ex := outside_hit c (w := stop c q + u) hq (by omega) (by omega) (Or.inr (by omega)) j
    simpa using ex
  cases minus <;> fin_cases i
  · exact legal 0 (by decide) 0
  · exact legal 0 (by decide) 2
  · exact legal 1 (by decide) 2
  · exact legal 0 (by decide) 3
  · exact legal 0 (by decide) 1
  · exact legal 1 (by decide) 1

/-- After the first omission every remaining interior state belongs to one of
the two triples at its own coordinate. Following the suffix reaches a retained exit. -/
theorem drains {sw : ℕ → Bool} (h : LocalPaths c F N E K χ sw) (hq : 65 ≤ q)
    (x : Family.Label m) : ∃ y, Reach (onFrames F) x.val (retained c m N E y) := by
  obtain ⟨w, hw, hwq, j, path⟩ := h.drain x
  by_cases hout : w < start c ∨ stop c q ≤ w
  · obtain ⟨y, hy⟩ := outside_hit c hq hw hwq hout j
    exact ⟨y, by simpa only [retained, hy] using path⟩
  · let k := w - start c
    have hk : k < length c q := by dsimp [stop, k] at *; omega
    have wk : start c + k = w := by dsimp [k]; omega
    have address : ∃ (minus : Bool) (i : Fin 2), currentSlot minus i = j.val := by
      fin_cases j
      · exact ⟨false, 0, rfl⟩
      · exact ⟨true, 1, rfl⟩
      · exact ⟨false, 1, rfl⟩
      · exact ⟨true, 0, rfl⟩
    obtain ⟨minus, i, hi⟩ := address
    obtain ⟨out, reach⟩ := chain_exit (fun l => layer c m N E l minus)
      (fun l hl i => ⟨_, interval_step h hq hl minus i⟩) hk.le i.castSucc
    obtain ⟨y, hy⟩ := exit_point (c := c) hq minus out
    refine ⟨y, path.trans ?_⟩
    simpa only [retained, hy, layer, wk, current_point, hi, stop] using reach

omit [Fact p.Prime] in
/-- The symbolic paths are computed on affine frames. A path beginning at a
connection label stays in the connection set, so it lifts to the rotation itself. -/
private theorem legal_of_reach (F : Family.Complete m ι) (x : Family.Label m) {y : Frame p q}
    (h : Reach (onFrames F) x.val y) : separated m.power y = true := by
  obtain ⟨n, rfl⟩ := h
  have sc : Function.Semiconj Subtype.val F.rho (onFrames F) :=
    fun z => (Equiv.Perm.ofSubtype_apply_coe _ z).symm
  rw [← sc.iterate_right n x]
  exact (F.rho^[n] x).property

private theorem lift_cycle {c : Case} (F : Family.Complete m ι) (N E : Fin q)
    (g : Boundary.Label c → Boundary.Label c) (cycle : OneCycle g)
    (edges : Routes (onFrames F) g (retained c m N E))
    (hits : ∀ x : Family.Label m, ∃ y, Reach (onFrames F) x.val (retained c m N E y)) :
    OneCycle F.rho := by
  classical
  by_cases ne : Nonempty (Family.Label m)
  · obtain ⟨x⟩ := ne
    obtain ⟨base, hbase⟩ := hits x
    let embed (y : Boundary.Label c) : Family.Label m :=
      ⟨retained c m N E y, legal_of_reach F x (hbase.trans (edges.lift (cycle base y)))⟩
    apply oneCycle_of_contraction (port := embed) (g := g) _ _ cycle
    · exact fun y => (reach_onFrames_iff F _ _).mp (edges y)
    · intro x
      obtain ⟨y, hy⟩ := hits x
      exact ⟨y, (reach_onFrames_iff F _ _).mp hy⟩
  · exact fun x => (ne ⟨x⟩).elim

/-- A single orbit of the actual bounded step lifts through the two omissions. -/
theorem oneCycle_of_boundary {mask : ℕ} {s : ℕ → Bool} {a b : Interval.Perm}
    (h : LocalPaths c F N E K χ (switches c q mask s)) (hq : 65 ≤ q)
    (ha : forward (fun k => χ (start c + k)) s false (length c q) = a)
    (hb : forward (fun k => χ (start c + k)) s true (length c q) = b)
    (cycle : OneCycle (step c (pattern c q χ) mask a b)) : OneCycle F.rho :=
  lift_cycle F N E _ cycle (routes h hq ha hb) (drains h hq)

end BipartiteKneser.Reduction
