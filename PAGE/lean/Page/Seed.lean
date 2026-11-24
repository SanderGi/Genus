/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.Certificate

/-! # A facial certificate for the input neighbor orders -/

@[expose] public section

namespace Page.Seed

open MultiGenus MultiGenus.Faces MultiGenus.Rotations Page.Certificate

/-- The upper-bound rotation uses the neighbors in input order at every vertex. -/
def inputRows (n : Nat) (edges : List Edge) : Rows := (List.range n).map (neighbors edges)

theorem inputRows_legal (n : Nat) (edges : List Edge) : Legal n edges (inputRows n edges) :=
  (mem_enumerate_iff ..).mp (adjacency_mem_enumerate n edges)

/-- Traverse the face once, starting with the chosen dart. -/
def trace (r : Rows) (d : Edge) : Face := List.iterate (faceStep r) d (faceWalk r d).card

private theorem iterate_face {r} (valid : Valid r) (d : Dart r) (k : Nat) :
    List.iterate (faceStep r) d.val k =
      (List.iterate (facePerm valid) d k).map Subtype.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    exact congrArg (d.val :: ·) (ih (facePerm valid d))

private theorem trace_word {r} (valid : Valid r) (x : Dart r) :
    trace r x.val = (OrbitWords.word (facePerm valid) x).map Subtype.val := by
  let p := facePerm valid
  have key : faceWalk r x.val = ((OrbitWords.word p x).map Subtype.val).toFinset := by
    ext z
    simp only [mem_faceWalk valid, List.mem_toFinset, List.mem_map, OrbitWords.mem_word]
    exact exists_congr fun _ => and_comm
  have card := congrArg Finset.card key
  rw [List.toFinset_card_of_nodup ((OrbitWords.nodup_word ..).map Subtype.val_injective),
    List.length_map] at card
  rw [trace, card, iterate_face valid]
  congr 1
  change List.iterate p x (OrbitWords.word p x).length = OrbitWords.word p x
  by_cases fixed : p x = x
  · simp [OrbitWords.word, fixed]
  · simp only [OrbitWords.word, fixed, ↓reduceIte, Equiv.Perm.length_toList]
    rfl

private theorem mem_trace {r} (valid : Valid r) (d : Dart r) (z : Edge) :
    z ∈ trace r d.val ↔ ∃ x : Dart r, x.val = z ∧ (facePerm valid).SameCycle d x := by
  rw [trace_word valid, List.mem_map]
  exact exists_congr fun x => by rw [OrbitWords.mem_word]; exact and_comm

private theorem trace_self {r} (valid : Valid r) (d : Dart r) : d.val ∈ trace r d.val :=
  (mem_trace valid ..).mpr ⟨d, rfl, .rfl⟩

private theorem trace_nodup {r} (valid : Valid r) (d : Dart r) : (trace r d.val).Nodup := by
  rw [trace_word valid]
  exact (OrbitWords.nodup_word ..).map Subtype.val_injective

private theorem trace_step {r} (valid : Valid r) (d : Dart r) (z : Edge) (hz : z ∈ trace r d.val) :
    (trace r d.val).formPerm z = faceStep r z := by
  rw [trace_word valid] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  rw [OrbitWords.formPerm_map_apply _ Subtype.val_injective _ (OrbitWords.nodup_word ..) _ hx,
    OrbitWords.step_word _ _ x hx]
  rfl

/-- Trace the first remaining dart and remove all darts of its face before continuing. -/
def collect (r : Rows) : Nat → List Edge → List Face
  | 0, _ | _ + 1, [] => []
  | k + 1, d :: ds =>
    let f := trace r d
    f :: collect r k (ds.filter fun x => x ∉ f)

private theorem collect_spec {r} (valid : Valid r) (k : Nat) (ds : List Edge)
    (bound : ds.length ≤ k) (nd : ds.Nodup) (dartsIn : ∀ d ∈ ds, d ∈ darts r)
    (closed : ∀ d ∈ ds, ∀ x ∈ trace r d, x ∈ ds) :
    (collect r k ds).flatten.Perm ds ∧
      ∀ f ∈ collect r k ds, ∃ x : Dart r, f = trace r x.val := by
  induction k generalizing ds with
  | zero =>
    have eq : ds = [] := by simpa using bound
    subst ds
    simp [collect]
  | succ k ih =>
    cases ds with
    | nil => simp [collect]
    | cons d ds =>
      let x : Dart r := ⟨d, dartsIn d (.head _)⟩
      let w := trace r d
      let rest := ds.filter fun a => a ∉ w
      have sub (a : Edge) (ha : a ∈ rest) := (List.mem_filter.mp ha).1
      have apart (a : Edge) (ha : a ∈ rest) : a ∉ w :=
        of_decide_eq_true (List.mem_filter.mp ha).2
      have origin : d ∈ w := trace_self valid x
      have keep {a : Edge} (ha : a ∈ d :: ds) (hw : a ∉ w) : a ∈ rest := by
        exact List.mem_filter.mpr ⟨(List.mem_cons.mp ha).resolve_left (fun eq => hw (eq ▸ origin)),
          decide_eq_true hw⟩
      have hrest (a : Edge) (ha : a ∈ rest) (b : Edge) (hb : b ∈ trace r a) : b ∈ rest := by
        have old : a ∈ d :: ds := .tail _ (sub _ ha)
        let y : Dart r := ⟨a, dartsIn _ old⟩
        apply keep (closed a old b hb)
        intro hw
        obtain ⟨z, hz, hxz⟩ := (mem_trace valid x b).mp hw
        obtain ⟨z', hz', hyz⟩ := (mem_trace valid y b).mp hb
        have eq : z' = z := Subtype.ext (hz'.trans hz.symm)
        subst z'
        exact apart _ ha ((mem_trace valid x a).mpr ⟨y, rfl, hxz.trans hyz.symm⟩)
      have smaller : rest.length ≤ k := le_trans (List.length_filter_le _ _) (by simpa using bound)
      obtain ⟨perm, fromDart⟩ := ih rest smaller ((List.nodup_cons.mp nd).2.filter _)
        (fun a ha => dartsIn _ (.tail _ (sub a ha))) hrest
      have partition : (w ++ rest).Perm (d :: ds) := by
        refine List.perm_of_nodup_nodup_toFinset_eq ?_ nd ?_
        · apply List.nodup_append.mpr
          exact ⟨trace_nodup valid x, (List.nodup_cons.mp nd).2.filter _,
            fun a ha b hb eq => apart b hb (eq ▸ ha)⟩
        · ext a
          simp only [List.mem_toFinset, List.mem_append]
          constructor
          · exact fun h => h.elim (closed d (.head _) a) (fun ha => .tail _ (sub a ha))
          · intro ha
            by_cases hw : a ∈ w
            · exact Or.inl hw
            · exact Or.inr (keep ha hw)
      refine ⟨(perm.append_left w).trans partition, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨x, rfl⟩
      · exact fromDart _ hf

/-- A deterministic orientable embedding certificate, using the row order supplied by the input. -/
def inputFaces (n : Nat) (edges : List Edge) : List Face :=
  if n = 1 ∧ edges = [] then [[]] else
    collect (inputRows n edges) (Certificate.universe edges).length (Certificate.universe edges)

private theorem input_partition {n edges} (G : SimpleInput n edges) (hi : ¬ (n = 1 ∧ edges = [])) :
    Partition edges (inputFaces n edges) ∧ Matches (inputRows n edges) (inputFaces n edges) := by
  let r := inputRows n edges
  have legal := inputRows_legal n edges
  have valid := valid_of_legal G legal
  have inc (d : Edge) := dart_iff legal G d
  have closed (d : Edge) (hd : d ∈ Certificate.universe edges) (x : Edge) (hx : x ∈ trace r d) :
      x ∈ Certificate.universe edges := by
    obtain ⟨z, rfl, _⟩ := (mem_trace valid ⟨d, (inc _).mpr hd⟩ x).mp hx
    exact (inc _).mp z.prop
  obtain ⟨cover, words⟩ := collect_spec valid _ _ le_rfl (universe_nodup G)
    (fun d hd => (inc d).mpr hd) closed
  simp only [inputFaces, hi, ↓reduceIte]
  refine ⟨⟨cover, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨x, rfl⟩ := words f hf
    exact ⟨List.ne_nil_of_mem (trace_self valid x), trace_nodup valid x⟩
  · intro f hf d hd
    obtain ⟨x, rfl⟩ := words f hf
    exact trace_step valid x d hd

/-- The canonical seed is accepted by the executable verifier, including the isolated vertex. -/
theorem check_inputFaces {n edges} (G : SimpleInput n edges) :
    check n edges (inputFaces n edges) = true := by
  rw [check_iff]
  split
  · rename_i h
    simp [inputFaces, h]
  · rename_i h
    obtain ⟨part, m⟩ := input_partition G h
    have legal := inputRows_legal n edges
    exact ⟨part, _, legal, fun v _ => (valid_of_legal G legal).nodup v, m⟩

/-- Tracing the input rotation returns exactly its executable number of faces. -/
theorem length_inputFaces {n edges} (G : SimpleInput n edges) :
    (inputFaces n edges).length = faceCount (inputRows n edges) := by
  by_cases h : n = 1 ∧ edges = []
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · obtain ⟨part, turns⟩ := input_partition G h
    have legal := inputRows_legal n edges
    have ne : inputRows n edges ≠ [[]] := by
      intro eq
      have hn : n = 1 := legal.1 ▸ congrArg List.length eq
      apply h
      refine ⟨hn, List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_⟩
      have := G.ordered e he
      have := G.bounded e he
      omega
    simpa only [faceCount, ne, ↓reduceIte] using (orbitCount_partition G part legal turns).symm

end Page.Seed
