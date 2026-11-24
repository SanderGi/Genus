/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.MultiCode
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas
import Mathlib.Data.List.Nodup

/-! # Graph6 records and mixed-width multicode streams for HoG -/

@[expose] public section

namespace HoG.Input

open MultiGenus MultiGenus.Rotations MultiGenus.MultiCode

/-- An order and a list of upper-triangular edges numbered from zero. -/
abbrev Graph := Nat × List Edge

/-- Number of adjacency bits for a graph6 record on `n` vertices. -/
def triangle (n : Nat) := n * (n - 1) / 2

/-- Canonical short or extended graph6 order prefix in ASCII. -/
def orderBytes (n : Nat) : List Nat :=
  if n < 63 then [63 + n]
  else [126, 63 + n / 4096, 63 + n / 64 % 64, 63 + n % 64]

/-- Split the canonical graph6 order prefix from the remaining ASCII sextets. -/
def parseOrder : List Nat → Option (Nat × List Nat)
  | [] => none
  | x :: xs =>
    if x = 126 then
      match xs with
      | a :: b :: c :: rest =>
        let n := (a - 63) * 4096 + (b - 63) * 64 + (c - 63)
        if n ≤ 65535 ∧ [126, a, b, c] = orderBytes n ∧ 63 ≤ n
          then some (n, rest) else none
      | _ => none
    else if 64 ≤ x ∧ x ≤ 125 then some (x - 63, xs) else none

/-- The payload occupies exactly the required number of printable sextets. Its
unused low bits are zero, including the empty-payload case. -/
def ValidPayload (n : Nat) (data : List Nat) : Prop :=
  data.length = (triangle n + 5) / 6 ∧ (∀ x ∈ data, 63 ≤ x ∧ x ≤ 126) ∧
    (data.getLastD 63 - 63) % (2 ^ ((6 - triangle n % 6) % 6)) = 0

instance (n : Nat) (data : List Nat) : Decidable (ValidPayload n data) := by
  unfold ValidPayload
  infer_instance

/-- Read the MSB-first adjacency bit of a graph6 sextet array. Column `v`
starts after all unordered pairs on the first `v` vertices. -/
def graph6Bit (data : Array Nat) (u v : Nat) : Bool :=
  let k := triangle v + u
  (data[k / 6]?.getD 63 - 63).testBit (5 - k % 6)

/-- Enumerate the set bits in graph6 column order. -/
def graph6Edges (n : Nat) (data : Array Nat) : List Edge :=
  (List.range n).flatMap fun v => ((List.range v).filter (graph6Bit data · v)).map (·, v)

/-- A graph6 edge is present precisely at its encoded upper-triangular bit. -/
theorem mem_graph6Edges {n u v : Nat} {data : Array Nat} :
    (u, v) ∈ graph6Edges n data ↔ u < v ∧ v < n ∧ graph6Bit data u v := by
  simp [graph6Edges, and_assoc, and_comm, and_left_comm]

private theorem simple_graph6Edges (n : Nat) (data : Array Nat) :
    SimpleInput n (graph6Edges n data) := by
  refine ⟨fun ⟨_, _⟩ h => (mem_graph6Edges.mp h).1,
    fun ⟨_, _⟩ h => (mem_graph6Edges.mp h).2.1, List.nodup_flatMap.mpr ⟨?_, ?_⟩⟩
  · intro v _
    exact (List.nodup_range.filter _).map (fun _ _ e => congrArg Prod.fst e)
  · apply List.nodup_range.imp
    intro a b ne x ha hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, eq⟩ := List.mem_map.mp hb
    exact ne (congrArg Prod.snd eq).symm

/-- Decode one canonical ASCII graph6 record, without header or line ending. -/
def decodeGraph6 (bytes : List Nat) : Option Graph := do
  let (n, data) ← parseOrder bytes
  if ValidPayload n data then some (n, graph6Edges n data.toArray) else none

/-- The accepted order prefixes are precisely the short and extended canonical encodings
for positive orders through 65535, independently of the following payload. -/
theorem parseOrder_spec {bytes data : List Nat} {n : Nat} :
    parseOrder bytes = some (n, data) ↔
      1 ≤ n ∧ n ≤ 65535 ∧ bytes = orderBytes n ++ data := by
  constructor
  · intro h
    cases bytes with
    | nil => simp [parseOrder] at h
    | cons x xs =>
      simp only [parseOrder] at h
      split at h
      · subst x
        split at h <;> try contradiction
        split at h <;> try contradiction
        rename_i good
        cases h
        obtain ⟨hi, header, lo⟩ := good
        exact ⟨by omega, hi, congrArg (· ++ _) header⟩
      · split at h <;> try contradiction
        rename_i good
        cases h
        have small : x - 63 < 63 := by omega
        exact ⟨by omega, by omega, by simp [orderBytes, small, show 63 + (x - 63) = x by omega]⟩
  · rintro ⟨lo, hi, rfl⟩
    unfold orderBytes
    split
    · rename_i small
      have ne : 63 + n ≠ 126 := by omega
      simp [parseOrder, ne, show 64 ≤ 63 + n by omega, show 63 + n ≤ 125 by omega]
    · rename_i big
      have calcN : n / 4096 * 4096 + n / 64 % 64 * 64 + n % 64 = n := by omega
      simp [parseOrder, calcN, hi, orderBytes, big, show 63 ≤ n by omega]

/-- Exact graph6 framing, payload validity and output, in both directions. -/
theorem decodeGraph6_spec {bytes : List Nat} {n : Nat} {edges : List Edge} :
    decodeGraph6 bytes = some (n, edges) ↔
      1 ≤ n ∧ n ≤ 65535 ∧ ∃ data, bytes = orderBytes n ++ data ∧ ValidPayload n data ∧
        edges = graph6Edges n data.toArray := by
  constructor
  · intro h
    obtain ⟨⟨m, p⟩, parsed, after⟩ := Option.bind_eq_some_iff.mp h
    change (if ValidPayload m p then some (m, graph6Edges m p.toArray) else none) = _ at after
    split at after <;> simp_all only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl⟩ := after
    obtain ⟨lo, hi, eq⟩ := parseOrder_spec.mp parsed
    exact ⟨lo, hi, p, eq, ‹_›, rfl⟩
  · rintro ⟨lo, hi, p, eq, good, rfl⟩
    simp [decodeGraph6, parseOrder_spec.mpr ⟨lo, hi, eq⟩, good]

/-- At a known record boundary, decoding reads exactly the designated payload bit for
each unordered pair of vertices. -/
theorem decodeGraph6_edge_iff {n u v : Nat} {data : List Nat} {edges : List Edge}
    (h : decodeGraph6 (orderBytes n ++ data) = some (n, edges)) :
    (u, v) ∈ edges ↔ u < v ∧ v < n ∧ graph6Bit data.toArray u v := by
  obtain ⟨_, _, p, eq, _, rfl⟩ := decodeGraph6_spec.mp h
  obtain rfl : data = p := List.append_cancel_left eq
  exact mem_graph6Edges

/-- Every accepted graph6 record describes a simple graph on the indicated vertices. -/
theorem decodeGraph6_simple {bytes : List Nat} {n : Nat} {es : List Edge}
    (h : decodeGraph6 bytes = some (n, es)) : SimpleInput n es := by
  obtain ⟨_, _, p, _, _, rfl⟩ := decodeGraph6_spec.mp h
  exact simple_graph6Edges _ _

/-- Serialize 16-bit words low byte first. For valid rows all values fit in two bytes. -/
def littleEndian (words : List Nat) : List Nat :=
  words.flatMap fun x => [x % 256, x / 256]

/-- Unpack pairs, leaving any final unpaired byte for a later record. -/
def wideWords : List Nat → List Nat
  | a :: b :: rest => (a + 256 * b) :: wideWords rest
  | _ => []

private theorem wideWords_append (ws rest : List Nat) :
    wideWords (littleEndian ws ++ rest) = ws ++ wideWords rest := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    change (x % 256 + 256 * (x / 256)) :: wideWords (littleEndian xs ++ rest) = _
    rw [Nat.mod_add_div, ih]
    rfl

private theorem readRows_length {k : Nat} {bs rest : List Nat} {rs : List (List Nat)}
    (h : readRows k bs = some (rs, rest)) : rs.length = k := by
  induction k generalizing bs rs with
  | zero => cases h; rfl
  | succ k ih =>
    obtain ⟨⟨vs, t⟩, _, after⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨xs, s⟩, parsed, eq⟩ := Option.map_eq_some_iff.mp after
    cases eq
    simp [ih parsed]

private theorem readRows_body (rs : List (List Nat)) (rest : List Nat) :
    readRows rs.length (body rs ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons vs rs ih =>
    have row (t : List Nat) : readRow (vs.map Nat.succ ++ 0 :: t) = some (vs, t) := by
      have good : ∀ x ∈ vs.map Nat.succ, (x != 0) = true := by simp
      simp [readRow, List.dropWhile_append_of_pos good, List.takeWhile_append_of_pos good,
        List.map_map, Function.comp_def]
    simpa [body, readRows, List.append_assoc, row] using ih

/-- A multicode record's bytes and edge semantics. The width is selected anew
for each record, and the last vertex has an implicit empty row. -/
def Record (wide : Bool) (chunk : List Nat) (g : Graph) : Prop :=
  (if wide then 256 ≤ g.1 ∧ g.1 ≤ 65535 else 1 ≤ g.1 ∧ g.1 ≤ 255) ∧
    ∃ rs, rs.length = g.1 - 1 ∧ ValidRows g.1 0 rs ∧ g.2 = canonicalEdges 0 rs ∧
      chunk = (if wide then littleEndian (g.1 :: body rs) else g.1 :: body rs)

/-- Decode a wide record. Checking the original byte prefix also rejects values
outside byte range when called with an unrestricted list of naturals. -/
def decodeWide (bytes : List Nat) : Option (Graph × List Nat) := do
  let a :: b :: tail := bytes | none
  let n := a + 256 * b
  if ¬(256 ≤ n ∧ n ≤ 65535) then none else
    let (rs, _) ← readRows (n - 1) (wideWords tail)
    if ValidRows n 0 rs then
      let chunk := littleEndian (n :: body rs)
      if bytes.take chunk.length = chunk then
        some ((n, canonicalEdges 0 rs), bytes.drop chunk.length)
      else none
    else none

private theorem decodeWide_spec {bs rest : List Nat} {g : Graph} :
    decodeWide bs = some (g, rest) ↔ ∃ chunk, Record true chunk g ∧ bs = chunk ++ rest := by
  constructor
  · intro h
    unfold decodeWide at h
    split at h <;> try contradiction
    dsimp only at h
    split at h <;> try contradiction
    obtain ⟨⟨rs, t⟩, parsed, after⟩ := Option.bind_eq_some_iff.mp h
    change (if _ then (if _ then some _ else none) else none) = _ at after
    split at after <;> try contradiction
    split at after <;> try contradiction
    rename_i framing
    cases after
    exact ⟨_, ⟨by simpa using not_not.mp ‹¬¬_›, rs, readRows_length parsed, ‹_›, rfl, rfl⟩,
      (List.take_append_drop _ _).symm.trans (congrArg (· ++ _) framing)⟩
  · rintro ⟨chunk, ⟨size, rs, len, valid, edges, rfl⟩, rfl⟩
    obtain ⟨n, es⟩ := g
    dsimp at size edges len valid ⊢
    subst es
    have read := readRows_body rs (wideWords rest)
    rw [len] at read
    have words : littleEndian (n :: body rs) =
        n % 256 :: n / 256 :: littleEndian (body rs) := rfl
    simp [words, decodeWide, Nat.mod_add_div, size, wideWords_append, read, valid,
      List.take_succ_cons, List.drop_succ_cons]

/-- Consume one record at the specified width, returning the untouched byte suffix. -/
def decodeRecord (wide : Bool) (bytes : List Nat) : Option (Graph × List Nat) :=
  if wide then decodeWide bytes else
    (decodeOne bytes).toOption.map fun (n, es, rest) => ((n, es), rest)

/-- Each fixed-width decoder accepts exactly its serialized rows, independently
of the following bytes. In particular a wide record may have an odd-length suffix. -/
theorem decodeRecord_spec {wide : Bool} {bytes rest : List Nat} {g : Graph} :
    decodeRecord wide bytes = some (g, rest) ↔
      ∃ chunk, Record wide chunk g ∧ bytes = chunk ++ rest := by
  cases wide with
  | true => exact decodeWide_spec
  | false =>
    obtain ⟨n, es⟩ := g
    simp only [decodeRecord, Bool.false_eq_true, ↓reduceIte, Record, Option.map_eq_some_iff]
    constructor
    · rintro ⟨⟨m, edges, r⟩, h, eq⟩
      cases eq
      have decoded : decodeOne bytes = .ok (m, edges, r) := by
        cases e : decodeOne bytes <;> simp_all [Except.toOption]
      obtain ⟨lo, hi, rs, len, valid, bytesEq, rfl⟩ := decodeOne_spec.mp decoded
      exact ⟨_, ⟨⟨lo, hi⟩, rs, len, valid, rfl, rfl⟩, bytesEq⟩
    · rintro ⟨_, ⟨⟨lo, hi⟩, rs, len, valid, rfl, rfl⟩, eq⟩
      have decoded := decodeOne_spec.mpr ⟨lo, hi, rs, len, valid, eq, rfl⟩
      exact ⟨(n, canonicalEdges 0 rs, rest), by simp [decoded, Except.toOption], rfl⟩

private theorem canonical_origin {rs : List (List Nat)} {a u v : Nat}
    (h : (u, v) ∈ canonicalEdges a rs) : a ≤ u := by
  induction rs generalizing a with
  | nil => simp [canonicalEdges] at h
  | cons row rs ih =>
    obtain h | h := List.mem_append.mp h
    · obtain ⟨_, _, eq⟩ := List.mem_map.mp h
      exact Nat.le_of_eq (congrArg Prod.fst eq)
    · exact Nat.le_trans (Nat.le_succ a) (ih h)

/-- Sorting rows preserves precisely the neighbors recorded at each row index. -/
theorem canonicalEdges_row (rs : List (List Nat)) (a k v : Nat) :
    (a + k, v) ∈ canonicalEdges a rs ↔ ∃ vs, rs[k]? = some vs ∧ v ∈ vs := by
  induction rs generalizing a k with
  | nil => simp [canonicalEdges]
  | cons row rs ih =>
    cases k with
    | zero =>
      have ht : (a, v) ∉ canonicalEdges (a+1) rs := fun h => by
        have := canonical_origin h
        omega
      simp [canonicalEdges, ht]
    | succ k =>
      have ne : a ≠ a + 1 + k := by omega
      simp [canonicalEdges, ne, show a + (k + 1) = a + 1 + k by omega, ih]

/-- The encoded rows determine adjacency in the returned graph at either word width.
Every boundary includes exactly one zero terminator for each explicit row. -/
theorem Record.adjacency {wide : Bool} {chunk : List Nat} {g : Graph} (h : Record wide chunk g) :
    ∃ rs, rs.length = g.1 - 1 ∧ ValidRows g.1 0 rs ∧ (body rs).count 0 = g.1 - 1 ∧
      chunk = (if wide then littleEndian (g.1 :: body rs) else g.1 :: body rs) ∧
      ∀ u v, (u, v) ∈ g.2 ↔ ∃ row, rs[u]? = some row ∧ v ∈ row := by
  obtain ⟨_, rs, len, good, edges, bytes⟩ := h
  refine ⟨rs, len, good, (body_count_zero _).trans len, bytes, ?_⟩
  intro u v
  simpa [edges] using canonicalEdges_row rs 0 u v

/-- A sequence of complete records, with their graph results in stream order. -/
inductive Records : List Nat → List Graph → Prop
  | nil : Records [] []
  | snoc {pre gs wide chunk g} : Records pre gs → Record wide chunk g →
      Records (pre ++ chunk) (gs ++ [g])

/-- Every record in a faithful segmentation gives a simple graph. -/
theorem Records.simple {bs gs} (h : Records bs gs) : ∀ g ∈ gs, SimpleInput g.1 g.2 := by
  induction h with
  | nil => simp
  | snoc prior last ih =>
    intro g hg
    obtain h | h := List.mem_append.mp hg
    · exact ih _ h
    · obtain rfl := List.mem_singleton.mp h
      obtain ⟨_, rows, _, valid, eq, _⟩ := last
      rw [eq]
      exact simpleInput_of_validRows valid

/-- The first segmentation reaching each record boundary, indexed by the number
of remaining bytes. Lists of decoded graphs are accumulated in reverse. -/
abbrev Boundaries := Std.HashMap Nat (List Graph)

/-- Try one width from a reachable boundary, retaining any earlier predecessor. -/
def tryWidth (wide : Bool) (suffix : List Nat) (rev : List Graph) (m : Boundaries) : Boundaries :=
  match decodeRecord wide suffix with
  | none => m
  | some (g, rest) => m.insertIfNew rest.length (g :: rev)

/-- Visit potential record starts from left to right, trying narrow before wide at a tie. -/
def scan : List Nat → Nat → Boundaries → Boundaries
  | [], _, m => m
  | x :: xs, k, m =>
    let next := match m[k]? with
      | none => m
      | some gs => tryWidth true (x :: xs) gs (tryWidth false (x :: xs) gs m)
    scan xs (k - 1) next

/-- Remove the optional HoG multicode stream header. -/
def multiCodeBody (bytes : List Nat) : List Nat :=
  let header := ">>multi_code<<".toList.map Char.toNat
  if header.isPrefixOf bytes then bytes.drop header.length else bytes

/-- Decode a nonempty HoG multicode stream. Reachable boundaries, including the
end of input, determine the widths in streams with ambiguous local prefixes. -/
def decodeMultiCode (bytes : List Nat) : Option (List Graph) :=
  let bs := multiCodeBody bytes
  if bs.isEmpty then none else
    ((scan bs bs.length ((∅ : Boundaries).insert bs.length []))[0]?).map List.reverse

private def Sound (raw : List Nat) (m : Boundaries) : Prop :=
  ∀ {k gs}, m[k]? = some gs → Records (raw.take (raw.length - k)) gs.reverse

private theorem tryWidth_sound {raw pre suffix : List Nat} {rev : List Graph} {m : Boundaries}
    (wide : Bool) (eq : raw = pre ++ suffix) (prior : Records pre rev.reverse)
    (ok : Sound raw m) : Sound raw (tryWidth wide suffix rev m) := by
  intro k gs h
  unfold tryWidth at h
  split at h
  · exact ok h
  · rename_i g rest parsed
    rw [Std.HashMap.getElem?_insertIfNew] at h
    split at h
    · rename_i new
      obtain rfl : rest.length = k := by simpa using new.1
      cases h
      obtain ⟨chunk, record, rfl⟩ := decodeRecord_spec.mp parsed
      rw [eq, ← List.append_assoc]
      rw [List.length_append, Nat.add_sub_cancel_right, List.take_left,
        List.reverse_cons]
      exact Records.snoc prior record
    · exact ok h

private theorem scan_sound {raw suffix : List Nat} {m : Boundaries} (ok : Sound raw m)
    {pre : List Nat} (eq : raw = pre ++ suffix) : Sound raw (scan suffix suffix.length m) := by
  induction suffix generalizing m pre with
  | nil => exact ok
  | cons x xs ih =>
    rw [scan]
    simp only [List.length_cons, Nat.add_sub_cancel]
    refine ih (pre := pre ++ [x]) ?_ (by simpa [List.append_assoc] using eq)
    split
    · exact ok
    · rename_i rev h
      have prior := ok h
      rw [eq] at prior
      simp only [List.length_append, List.length_cons, Nat.add_sub_cancel_right,
        List.take_left] at prior
      intro k gs read
      exact tryWidth_sound true eq prior (tryWidth_sound false eq prior ok) read

/-- Successful mixed-width decoding partitions the complete post-header body
into adjoining serialized records with the indicated edge lists. -/
theorem decodeMultiCode_records {bytes : List Nat} {gs : List Graph}
    (h : decodeMultiCode bytes = some gs) : Records (multiCodeBody bytes) gs := by
  let bs := multiCodeBody bytes
  change (if bs.isEmpty then none else _) = some gs at h
  split at h <;> try contradiction
  obtain ⟨rev, found, rfl⟩ := Option.map_eq_some_iff.mp h
  have init : Sound bs ((∅ : Boundaries).insert bs.length []) := by
    intro k gs h
    simp only [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i same
      have := beq_iff_eq.mp same
      subst k
      cases h
      simpa using Records.nil
    · simp at h
  have final := scan_sound init (pre := []) (suffix := bs) (by simp) found
  simpa [bs] using final

/-- Every graph returned by the stream decoder is a valid simple input. -/
theorem decodeMultiCode_simple {bytes : List Nat} {gs : List Graph}
    (h : decodeMultiCode bytes = some gs) (g : Graph) (hg : g ∈ gs) : SimpleInput g.1 g.2 :=
  (decodeMultiCode_records h).simple g hg

private theorem Record.nonempty {w c g} (h : Record w c g) : c ≠ [] := by
  obtain ⟨_, rs, _, _, _, rfl⟩ := h
  cases w <;> simp [littleEndian]

private theorem Records.first {bs gs} (h : Records bs gs) (hne : bs ≠ []) :
    ∃ w c g rest tail, Record w c g ∧ Records rest tail ∧ bs = c ++ rest := by
  induction h with
  | nil => contradiction
  | @snoc pre gs wide chunk g prior last ih =>
    by_cases hp : pre = []
    · subst pre
      exact ⟨_, _, _, [], [], last, .nil, by simp⟩
    · obtain ⟨w, c, a, rest, tail, ha, ht, rfl⟩ := ih hp
      exact ⟨w, c, a, _, _, ha, ht.snoc last, List.append_assoc ..⟩

private theorem tryWidth_mem {k w bs rev m} :
    k ∈ tryWidth w bs rev m ↔ k ∈ m ∨
      ∃ g rest, decodeRecord w bs = some (g, rest) ∧ rest.length = k := by
  unfold tryWidth
  split
  · simp_all
  · simp_all [or_comm]

private theorem scan_complete (bs : List Nat) (m : Boundaries)
    (path : ∃ tail gs, tail <:+ bs ∧ tail.length ∈ m ∧ Records tail gs) :
    0 ∈ scan bs bs.length m := by
  induction bs generalizing m with
  | nil =>
    obtain ⟨tail, _, h, seen, _⟩ := path
    obtain rfl : tail = [] := by simpa using h
    exact seen
  | cons x xs ih =>
    obtain ⟨tail, gs, suffix, seen, parsed⟩ := path
    rw [scan]
    simp only [List.length_cons, Nat.add_sub_cancel]
    apply ih
    obtain rfl | smaller := List.suffix_cons_iff.mp suffix
    · obtain ⟨w, c, g, rest, tail, record, more, eq⟩ := parsed.first (by simp)
      have step := decodeRecord_spec.mpr ⟨c, record, eq⟩
      have suffix' : rest <:+ xs := by
        cases c with
        | nil => exact (record.nonempty rfl).elim
        | cons a c =>
          exact ⟨c, (List.cons.inj eq).2.symm⟩
      have present := Std.HashMap.mem_iff_isSome_getElem?.mp seen
      split
      · rename_i missing
        simp only [List.length_cons, missing, Option.isSome_none, Bool.false_eq_true] at present
      · refine ⟨rest, tail, suffix', ?_, more⟩
        cases w with
        | false => exact tryWidth_mem.mpr (.inl (tryWidth_mem.mpr (.inr ⟨g, rest, step, rfl⟩)))
        | true => exact tryWidth_mem.mpr (.inr ⟨g, rest, step, rfl⟩)
    · refine ⟨tail, gs, smaller, ?_, parsed⟩
      split
      · exact seen
      · exact tryWidth_mem.mpr (.inl (tryWidth_mem.mpr (.inl seen)))

/-- Mixed-width decoding succeeds exactly when the nonempty body can be
partitioned into valid records. Ambiguous streams use the first predecessor
of each end offset, as in the native scanner. -/
theorem decodeMultiCode_succeeds_iff (bytes : List Nat) :
    (∃ gs, decodeMultiCode bytes = some gs) ↔
      multiCodeBody bytes ≠ [] ∧ ∃ gs, Records (multiCodeBody bytes) gs := by
  constructor
  · rintro ⟨gs, h⟩
    refine ⟨?_, gs, decodeMultiCode_records h⟩
    intro empty
    simp [decodeMultiCode, empty] at h
  · rintro ⟨ne, gs, h⟩
    let bs := multiCodeBody bytes
    let init : Boundaries := (∅ : Boundaries).insert bs.length []
    have start : bs.length ∈ init := by simp [init]
    have reached := scan_complete bs init ⟨bs, gs, List.suffix_refl _, start, h⟩
    obtain ⟨rev, eq⟩ := Option.isSome_iff_exists.mp (Std.HashMap.mem_iff_isSome_getElem?.mp reached)
    refine ⟨rev.reverse, ?_⟩
    simpa [decodeMultiCode, ne, bs, init] using congrArg (Option.map List.reverse) eq

end HoG.Input
