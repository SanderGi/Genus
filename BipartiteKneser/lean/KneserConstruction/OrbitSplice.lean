module

public import KneserConstruction.OrbitCore
public import Mathlib.Data.Fin.VecNotation

/-! # Translation and zero-coordinate splices (Lemma 6.3)

A block has four slots in the order U, U⁻¹, V, V⁻¹.  Inverting a slot flips
its low bit. Blocks 0 and 1 are the input and output exponent pairs. The
other blocks are the translation or zero-coordinate pairs visited on the way.
The long chains are collapsed using their parity. All remaining steps below
come directly from the quadruples of Constructions 5.2 and 5.6. -/

@[expose] public section

namespace BipartiteKneser.Orbit.Splice

variable {α : Type*}

/-- Address in a four-element block. -/
def addr (b : ℕ) (i : Fin 4) := 4 * b + i.val

/-- Inverse partner in the same block. -/
def mate (x : ℕ) := x ^^^ 1

/-- A quadruple of symbolic addresses in the order a, b, c, d. -/
structure Row where
  /-- Source address whose image is d. -/
  a : ℕ
  /-- Source address whose image is the inverse partner of d. -/
  b : ℕ
  /-- Target address of the inverse partner of a. -/
  c : ℕ
  /-- Target address of a. -/
  d : ℕ
  deriving DecidableEq

/-- The four directed assignments of a symbolic quadruple, including those at inverse partners. -/
def Row.edges (r : Row) : List (ℕ × ℕ) :=
  [(r.a, r.d), (mate r.a, r.c), (r.b, mate r.d), (mate r.b, mate r.c)]

/-- Each listed pair describes a forward path. -/
def Valid (f : α → α) (label : ℕ → α) (edges : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ edges, Reach f (label e.1) (label e.2)

/-- Concatenating two valid edge lists preserves the path represented by each edge. -/
theorem valid_append {f : α → α} {label : ℕ → α} {u v : List (ℕ × ℕ)}
    (hu : Valid f label u) (hv : Valid f label v) : Valid f label (u ++ v) := by
  intro e he
  exact (List.mem_append.mp he).elim (hu e) (hv e)

-- A path stops at an unassigned exit.
private def next (edges : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((edges.find? (fun e => e.1 == i)).map Prod.snd).getD i

private theorem valid_next {f : α → α} {label : ℕ → α} {es : List (ℕ × ℕ)}
    (v : Valid f label es) : Routes f (next es) label := by
  intro i
  unfold next
  cases h : es.find? (fun e => e.1 == i) with
  | none => exact .refl _
  | some e =>
    have hi : e.1 = i := by simpa using List.find?_some h
    simpa [← hi] using v e (List.mem_of_find?_eq_some h)

/-- First quadruple Q(U, V;V', U') swaps the middle slots. -/
def first : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- Second quadruple Q(U, V;U'⁻¹, V'⁻¹) exchanges the outside slots. -/
def second : Fin 4 → Fin 4 := ![3, 1, 2, 0]

/-- An arbitrary run of first quadruples reduces to its parity. -/
theorem first_chain {f : α → α} (layer : ℕ → Fin 4 → α) {n : ℕ}
    (steps : ∀ t < n, Across f (layer t) (layer (t + 1)) first) :
    Across f (layer 0) (layer n) (fun i => if n % 2 = 0 then i else first i) := by
  induction n with
  | zero => intro i; exact .refl _
  | succ n ih =>
    intro i
    have h := (ih (fun t ht => steps t (by omega)) i).trans (steps n (by omega) _)
    have inv : ∀ j, first (first j) = j := by decide
    by_cases hn : n % 2 = 0
    · simpa [hn, show (n + 1) % 2 ≠ 0 by omega] using h
    · simpa [hn, show (n + 1) % 2 = 0 by omega, inv] using h

/-- The four edges summarized by a layer-to-layer transfer. -/
def span (a b : ℕ) (s : Fin 4 → Fin 4) : List (ℕ × ℕ) :=
  (List.finRange 4).map fun i => (addr a i, addr b (s i))

/-- A path for each slot of a transfer realizes all four edges in its span. -/
theorem valid_span {f : α → α} {label : ℕ → α} {a b : ℕ} {s : Fin 4 → Fin 4}
    (h : Across f (label ∘ addr a) (label ∘ addr b) s) : Valid f label (span a b s) := by
  rintro _ he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact h i

/-- Translation blocks 2, 3, 4, 5 stand for j₁, k₁, j₂, k₂ respectively. -/
def translationRows : List Row :=
  [⟨16, 19, 13, 22⟩, ⟨8, 2, 20, 5⟩, ⟨10, 0, 15, 7⟩]

/-- Block 3 goes directly to block 4. From block 5 to block 2 there is a
second quadruple followed by the even number r−4 of first quadruples. -/
def translationEdges :=
  translationRows.flatMap Row.edges ++ (span 3 4 first ++ span 5 2 second)

/-- At the zero-coordinate splice block 2 is the index 0. The following
blocks stand for the subsequent indices 1, .., L and block 6 stands for j. -/
def zeroRows (oddM : Bool) : List Row :=
  [⟨1, 25, 6, 8⟩, ⟨27, 3, 5, 11⟩] ++
    if oddM then [⟨8, 11, 12, 18⟩, ⟨12, 14, 15, 17⟩, ⟨16, 18, 21, 23⟩]
    else [⟨8, 12, 13, 17⟩, ⟨10, 14, 15, 19⟩]

/-- In either parity case there are an odd number of first quadruples
between the last template block and the exceptional index j. -/
def zeroEdges (oddM : Bool) :=
  (zeroRows oddM).flatMap Row.edges ++ span (if oddM then 5 else 4) 6 first

/-- The terminal map of the translation splice preserves the exponent and
negates the coordinate. -/
def translationExit : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The zero splice exchanges coordinate signs at the positive exponent,
and preserves them at the negative exponent. -/
def zeroExit : Fin 4 → Fin 4 := ![2, 1, 0, 3]

set_option maxRecDepth 4096 in
private theorem translation_eval : ∀ i : Fin 4,
    (next translationEdges)^[12] (addr 0 i) = addr 1 (translationExit i) := by decide

set_option maxRecDepth 4096 in
private theorem translation_drain : ∀ i : Fin 24,
    ∃ j : Fin 4, (next translationEdges)^[12] i.val = addr 1 j := by decide

set_option maxRecDepth 4096 in
private theorem zero_eval : ∀ (b : Bool) (i : Fin 4),
    (next (zeroEdges b))^[20] (addr 0 i) = addr 1 (zeroExit i) := by decide

set_option maxRecDepth 4096 in
private theorem zero_drain : ∀ (b : Bool) (i : Fin 28), (b = true ∨ i.val / 4 ≠ 5) →
    ∃ j : Fin 4, (next (zeroEdges b))^[20] i.val = addr 1 j := by decide

/-- The four translation paths and exhaustion of all retained translation slots. -/
theorem translation {f : α → α} {label : ℕ → α}
    (rows : Valid f label (translationRows.flatMap Row.edges))
    (short : Across f (label ∘ addr 3) (label ∘ addr 4) first)
    (long : Across f (label ∘ addr 5) (label ∘ addr 2) second) :
    Across f (label ∘ addr 0) (label ∘ addr 1) translationExit ∧
    ∀ i : Fin 24, ∃ j, Reach f (label i.val) (label (addr 1 j)) := by
  have h := valid_next (valid_append rows (valid_append (valid_span short) (valid_span long)))
  constructor
  · exact fun i => h.lift ⟨12, translation_eval i⟩
  · intro i
    obtain ⟨j, hj⟩ := translation_drain i
    exact ⟨j, h.lift ⟨12, hj⟩⟩

/-- The four paths at fiber 1 and exhaustion of the retained zero-coordinate slots. -/
theorem zero {f : α → α} {label : ℕ → α} (b : Bool)
    (rows : Valid f label ((zeroRows b).flatMap Row.edges))
    (long : Across f (label ∘ addr (if b then 5 else 4)) (label ∘ addr 6) first) :
    Across f (label ∘ addr 0) (label ∘ addr 1) zeroExit ∧
    ∀ i : Fin 28, (b = true ∨ i.val / 4 ≠ 5) →
      ∃ j, Reach f (label i.val) (label (addr 1 j)) := by
  have h := valid_next (valid_append rows (valid_span long))
  constructor
  · exact fun i => h.lift ⟨20, zero_eval b i⟩
  · intro i hi
    obtain ⟨j, hj⟩ := zero_drain b i hi
    exact ⟨j, h.lift ⟨20, hj⟩⟩

end BipartiteKneser.Orbit.Splice
