import KneserConstruction.OrbitSplice
import KneserConstruction.FamilyChains
import Mathlib.Tactic.FinCases

/-! # Reading all four orbit assignments from a complete family -/

noncomputable section

namespace BipartiteKneser.Orbit

open Family Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] {m : Multipliers p q} {ι : Type*}

/-- Extend the family permutation to frames to allow equations between coordinate
formulas without transporting membership proofs through every intermediate step. -/
def onFrames (F : Complete m ι) : Equiv.Perm (Frame p q) := Equiv.Perm.ofSubtype F.rho

/-- Between connection labels, forward reachability in the extended frame permutation agrees with
reachability in the family rotation. -/
theorem reach_onFrames_iff (F : Complete m ι) (x y : Label m) :
    Reach (onFrames F) x.val y.val ↔ Reach F.rho x y := by
  have comm : Function.Semiconj Subtype.val F.rho (onFrames F) :=
    fun z => (Equiv.Perm.ofSubtype_apply_coe _ z).symm
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext ((comm.iterate_right n x).trans hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (comm.iterate_right n x).symm.trans (congrArg Subtype.val hn)⟩

/-- A row occurs in the assembler, independently of its chosen row address. -/
def HasRow (F : Complete m ι) (Q : Quad (Frame p q)) := ∃ i, F.row i = Q

/-- A quadruple present in the family sends each of its four sources to the prescribed target. -/
theorem HasRow.assign {F : Complete m ι} {Q : Quad (Frame p q)} (h : HasRow F Q)
    (s : Slot) : onFrames F (Q.dom (inverse m) s) = Q.ran (inverse m) s := by
  obtain ⟨i, rfl⟩ := h
  rw [← F.domain_val i s]
  exact (Equiv.Perm.ofSubtype_apply_coe _ _).trans (F.rho_row i s)

/-- Read the concrete rows named by a finite splice calculation. -/
theorem valid_splice_rows (F : Complete m ι) (label : ℕ → Frame p q) (rs : List Splice.Row)
    (inverseLabel : ∀ i, label (Splice.mate i) = inverse m (label i))
    (rows : ∀ r ∈ rs, HasRow F ⟨label r.a, label r.b, label r.c, label r.d⟩) :
    Splice.Valid (onFrames F) label (rs.flatMap Splice.Row.edges) := by
  intro e he
  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
  have h := (rows r hr).assign
  simp only [Splice.Row.edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact .step (h (false, false))
  · exact .step (by simpa only [Quad.dom, Quad.ran, inverseLabel] using h (false, true))
  · exact .step (by simpa only [Quad.dom, Quad.ran, inverseLabel] using h (true, false))
  · exact .step (by simpa only [Quad.dom, Quad.ran, inverseLabel] using h (true, true))

/-- Four slots in a block with positive representatives U and V. -/
def pairBlock (u v : Frame p q) : Fin 4 → Frame p q := ![u, inverse m u, v, inverse m v]

/-- One ordinary first quadruple. -/
theorem first_row {F : Complete m ι} {u v u' v' : Frame p q}
    (h : HasRow F ⟨u, v, v', u'⟩) :
    Across (onFrames F) (pairBlock (m := m) u v) (pairBlock (m := m) u' v') Splice.first := by
  intro i
  fin_cases i
  · exact .step (h.assign (false, false))
  · exact .step (h.assign (false, true))
  · exact .step (h.assign (true, false))
  · exact .step (h.assign (true, true))

/-- One reversed translation quadruple. -/
theorem second_row {F : Complete m ι} {u v u' v' : Frame p q}
    (invol : ∀ x, inverse m (inverse m x) = x)
    (h : HasRow F ⟨u, v, inverse m u', inverse m v'⟩) :
    Across (onFrames F) (pairBlock (m := m) u v) (pairBlock (m := m) u' v') Splice.second := by
  intro i
  fin_cases i
  · exact .step (h.assign (false, false))
  · exact .step (h.assign (false, true))
  · apply Reach.step
    change onFrames F v = v'
    simpa only [Quad.dom, Quad.ran, invol] using h.assign (true, false)
  · apply Reach.step
    change onFrames F (inverse m v) = u'
    simpa only [Quad.dom, Quad.ran, invol] using h.assign (true, true)

variable [Fact p.Prime]

/-- The two orientations above both signs of a nonzero coordinate. -/
def fiber (m : Multipliers p q) (k : Fin q) (w : ZMod p) : Fin 4 → Frame p q :=
  pairBlock (m := m) (X m k w) (X m k (-w))

/-- Reversing the chosen exponent in a block reverses all four exponent signs. -/
def flipExp : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- Negating the chosen exponent exchanges the two exponent signs within each coordinate sign. -/
theorem fiber_neg (h2 : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ZMod p) (i : Fin 4) :
    fiber m (-k) w i = fiber m k w (flipExp i) := by
  fin_cases i <;> simp [fiber, pairBlock, flipExp, inverse_X' m h2]

/-- A sequence of canonical rows acts by the parity of its length and the XOR of its switches. -/
def fiberMove (oddLength switch : Bool) (i : Fin 4) : Fin 4 :=
  let j := if oddLength then Splice.first i else i
  if switch then flipExp j else j

private theorem move_cons : ∀ (o s t : Bool) (i : Fin 4),
    fiberMove o s (fiberMove true t i) = fiberMove (!o) (t ^^ s) i := by decide

/-- A canonical quadruple routes all four slots to the next exponent pair, with its target
orientation determined by the switch. -/
theorem canonical_path (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0)
    (k l : Fin q) (w : ZMod p) (s : Bool) (h : HasRow F (canonical m k l w s)) :
    Across (onFrames F) (fiber m k w) (fiber m l w) (fiberMove true s) := by
  cases s
  · exact first_row h
  · intro i
    exact (first_row h i).trans (by
      change Reach _ (fiber m (-l) w (Splice.first i)) _
      rw [fiber_neg h2]
      exact .refl _)

/-- Accumulated switch parity, counting the switches on sources only. -/
def switchTotal (s : Fin q → Bool) (k : Fin q) : List (Fin q) → Bool
  | [] => false
  | l :: ls => s k ^^ switchTotal s l ls

/-- The parity of the chain length and of its switches determines the four endpoint slots. Every
intermediate slot reaches the final pair. -/
theorem chain_paths (F : Complete m ι) (h2 : (2 : ZMod p) ≠ 0) (w : ZMod p)
    (s : Fin q → Bool) (k : Fin q) (ls : List (Fin q))
    (rows : ∀ Q ∈ chain m w s k ls, HasRow F Q) :
    Across (onFrames F) (fiber m k w) (fiber m (ls.getLastD k) w)
      (fiberMove (ls.length % 2 == 1) (switchTotal s k ls)) ∧
    ∀ e ∈ k :: ls, ∀ i, ∃ j, Reach (onFrames F) (fiber m e w i) (fiber m (ls.getLastD k) w j) := by
  induction ls generalizing k with
  | nil =>
    constructor
    · exact fun i => .refl _
    · simpa using fun i => Exists.intro i (Reach.refl (f := ⇑(onFrames F)) (fiber m k w i))
  | cons l ls ih =>
    have head := canonical_path F h2 k l w (s k) (rows _ (.head _))
    obtain ⟨tail, drain⟩ := ih l (fun Q h => rows Q (.tail _ h))
    have parity : ((ls.length + 1) % 2 == 1) = !(ls.length % 2 == 1) := by
      by_cases he : ls.length % 2 = 0 <;> simp_all <;> omega
    have path : Across (onFrames F) (fiber m k w) (fiber m (ls.getLastD l) w)
        (fiberMove (! (ls.length % 2 == 1)) (s k ^^ switchTotal s l ls)) := by
      intro i
      rw [← move_cons]
      exact (head i).trans (tail _)
    simp only [List.length_cons, List.getLastD_cons, parity, switchTotal]
    refine ⟨path, ?_⟩
    intro e he i
    rcases List.mem_cons.mp he with rfl | mem
    · exact ⟨_, path i⟩
    · exact drain e mem i

end BipartiteKneser.Orbit
