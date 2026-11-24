/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.OrbitWords
public import Page.Walks
import Mathlib.Data.List.GetD

/-! # Certificates of facial walks for orientable rotation systems -/

@[expose] public section

namespace Page.Certificate

open MultiGenus MultiGenus.Rotations MultiGenus.Faces

/-- A face lists its directed edges in traversal order, with implicit wraparound. -/
abbrev Face := List Edge

/-- All directed incidences of the input, in the two orientations. -/
def «universe» (edges : List Edge) := edges ++ edges.map Prod.swap

@[simp] theorem mem_universe {e : Edge} {edges : List Edge} :
    e ∈ «universe» edges ↔ e ∈ edges ∨ e.swap ∈ edges := by
  simp [«universe», Prod.swap_eq_iff_eq_swap]

theorem universe_nodup {n edges} (G : SimpleInput n edges) : («universe» edges).Nodup := by
  rw [«universe», List.nodup_append]
  refine ⟨G.nodup, G.nodup.map Prod.swap_injective, ?_⟩
  rintro x hx _ hy rfl
  obtain ⟨y, hym, rfl⟩ := List.mem_map.mp hy
  exact (Nat.lt_asymm (G.ordered y hym) (G.ordered _ hx))

/-- Each input dart occurs once, and each ordinary face is a nonempty simple dart word. -/
def Partition (edges : List Edge) (fs : List Face) : Prop :=
  fs.flatten.Perm («universe» edges) ∧ ∀ f ∈ fs, f ≠ [] ∧ f.Nodup

/-- The turn recorded by a face at every incoming dart is the successor in the vertex row. -/
def Matches (r : Rows) (fs : List Face) : Prop :=
  ∀ f ∈ fs, ∀ d ∈ f, f.formPerm d = faceStep r d

/-- Cyclic successor in the first face containing the given dart. -/
def successor (fs : List Face) (d : Edge) : Edge :=
  ((fs.find? (fun f => d ∈ f)).getD []).formPerm d

/-- Start at the first input neighbor and follow the recorded turns for exactly the degree. -/
def readRow (fs : List Face) (v : Nat) (ns : List Nat) : List Nat :=
  match ns with
  | [] => []
  | a :: tail => List.iterate (fun x => (successor fs (x, v)).2) a (tail.length + 1)

/-- Rows recovered from the candidate face words. -/
def readRows (n : Nat) (edges : List Edge) (fs : List Face) : Rows :=
  (List.range n).map fun v => readRow fs v (neighbors edges v)

/-- Verify a certificate on the dart-bearing part of the graph. -/
def ordinary (n : Nat) (edges : List Edge) (fs : List Face) : Bool :=
  let r := readRows n edges fs
  fs.flatten.isPerm («universe» edges) &&
    fs.all (fun f => !f.isEmpty && decide f.Nodup) &&
    (List.range n).all (fun v => (row r v).isPerm (neighbors edges v) && decide (row r v).Nodup) &&
    fs.all (fun f => f.all fun d => f.formPerm d == faceStep r d)

/-- Check dart coverage and the single cyclic order reconstructed at each vertex.
The isolated vertex has one empty face. -/
def check (n : Nat) (edges : List Edge) (fs : List Face) : Bool :=
  if n = 1 ∧ edges = [] then decide (fs = [[]]) else ordinary n edges fs

@[simp] theorem check_isolated {fs : List Face} : check 1 [] fs = true ↔ fs = [[]] := by
  simp [check]

private theorem ordinary_iff {n edges fs} :
    ordinary n edges fs = true ↔ Partition edges fs ∧
      Legal n edges (readRows n edges fs) ∧
      (∀ v < n, (row (readRows n edges fs) v).Nodup) ∧ Matches (readRows n edges fs) fs := by
  simp only [ordinary, Partition, Legal, Matches, readRows, List.length_map, List.length_range,
    true_and, Bool.and_eq_true, List.all_eq_true, List.isPerm_iff, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, decide_eq_true_eq, List.mem_range, beq_iff_eq, row]
  grind

private theorem successor_of_matches {r fs edges} (part : Partition edges fs) (m : Matches r fs)
    (d : Edge) (hd : d ∈ «universe» edges) : successor fs d = faceStep r d := by
  obtain ⟨f, hf, hdf⟩ := List.mem_flatten.mp (part.1.mem_iff.mpr hd)
  unfold successor
  cases h : fs.find? (fun f => decide (d ∈ f)) with
  | none =>
    have hn := List.find?_eq_none.mp h f hf
    simp [hdf] at hn
  | some w =>
    apply m w (List.mem_of_find?_eq_some h) d
    simpa using List.find?_some (p := fun f => decide (d ∈ f)) h

private theorem iterate_word (a : Nat) (t : List Nat) (nd : (a :: t).Nodup)
    (step : Nat → Nat) (h : ∀ x ∈ a :: t, step x = (a :: t).formPerm x) :
    List.iterate step a (a :: t).length = a :: t := by
  have iter (i : Nat) : step^[i] a = ((a :: t).formPerm ^ i) a := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]
      apply h
      rw [List.formPerm_pow_apply_head a t nd]
      exact List.getElem_mem ..
  apply List.ext_getElem (by simp)
  intro i _ hi
  rw [List.getElem_iterate, iter, List.formPerm_pow_apply_head a t nd]
  simp only [Nat.mod_eq_of_lt hi]

private theorem readRow_rotated {n edges fs r} (part : Partition edges fs) (m : Matches r fs)
    (hr : Legal n edges r) (nd : ∀ v < n, (row r v).Nodup) {v : Nat} (hv : v < n) :
    (row r v).IsRotated (readRow fs v (neighbors edges v)) := by
  have perm : (row r v).Perm (neighbors edges v) := hr.2 v hv
  cases ns : neighbors edges v with
  | nil =>
    rw [ns] at perm
    rw [List.perm_nil.mp perm]
    exact .refl _
  | cons a t =>
    have ha : a ∈ row r v := perm.mem_iff.mpr (ns ▸ List.mem_cons_self)
    obtain ⟨l, u, eq, _⟩ := List.eq_append_cons_of_mem ha
    have rot : (row r v).IsRotated (a :: (u ++ l)) := eq ▸ List.isRotated_append
    have hlen : (a :: (u ++ l)).length = t.length + 1 := by
      rw [← rot.perm.length_eq, perm.length_eq, ns]
      rfl
    have step (x : Nat) (hx : x ∈ a :: (u ++ l)) :
        (successor fs (x, v)).2 = (a :: (u ++ l)).formPerm x := by
      have member := mem_neighbors.mp (perm.mem_iff.mp (rot.mem_iff.mpr hx))
      rw [successor_of_matches part m _ (mem_universe.mpr member.symm)]
      exact congrFun (congrArg DFunLike.coe (List.formPerm_eq_of_isRotated (nd v hv) rot)) x
    rw [readRow, ← hlen, iterate_word _ _ (rot.nodup_iff.mp (nd v hv)) _ step]
    exact rot

private theorem row_readRows {n edges fs v} (hv : v < n) :
    row (readRows n edges fs) v = readRow fs v (neighbors edges v) := by
  simp [row, readRows, List.getD_eq_getElem?_getD, hv]

private theorem ordinary_of_matches {n edges fs r} (part : Partition edges fs)
    (hr : Legal n edges r)
    (nd : ∀ v < n, (row r v).Nodup) (m : Matches r fs) : ordinary n edges fs = true := by
  have rot {v} (hv : v < n) : (row r v).IsRotated (row (readRows n edges fs) v) := by
    rw [row_readRows hv]
    exact readRow_rotated part m hr nd hv
  apply ordinary_iff.mpr
  refine ⟨part, ⟨by simp [readRows], fun v hv => (rot hv).perm.symm.trans (hr.2 v hv)⟩,
    fun v hv => (rot hv).nodup_iff.mp (nd v hv), ?_⟩
  intro f hf d hd
  rw [m f hf d hd]
  unfold faceStep
  by_cases hv : d.2 < n
  · rw [List.formPerm_eq_of_isRotated (nd _ hv) (rot hv)]
  · have out : r.length ≤ d.2 := by rw [hr.1]; omega
    simp [row, readRows, List.getD_eq_getElem?_getD, List.getElem?_eq_none out, hv]

/-- The verifier accepts exactly the partitions whose turns form a single cyclic neighbor
order at every vertex, with a separate empty boundary for the isolated vertex. -/
theorem check_iff {n edges fs} : check n edges fs = true ↔
    if n = 1 ∧ edges = [] then fs = [[]] else
      Partition edges fs ∧ ∃ r, Legal n edges r ∧ (∀ v < n, (row r v).Nodup) ∧ Matches r fs := by
  unfold check
  split
  · simp
  · constructor
    · intro h
      obtain ⟨part, legal, nd, m⟩ := ordinary_iff.mp h
      exact ⟨part, _, legal, nd, m⟩
    · rintro ⟨part, r, legal, nd, m⟩
      exact ordinary_of_matches part legal nd m

/-- Successful certificates partition both directions of every edge, with multiplicity. -/
theorem check_flatten_perm {n edges fs} (h : check n edges fs = true) :
    fs.flatten.Perm («universe» edges) := by
  have good := check_iff.mp h
  split at good
  · rename_i hi
    obtain ⟨rfl, rfl⟩ := hi
    subst fs
    exact .refl _
  · exact good.1.1

/-- Every face accepted on a graph with edges is a dart-simple closed walk. -/
theorem check_face {n edges fs f} (he : edges ≠ []) (h : check n edges fs = true)
    (hf : f ∈ fs) : f ≠ [] ∧ f.Nodup ∧ f ⊆ «universe» edges ∧ ∀ d ∈ f, d.2 = (f.formPerm d).1 := by
  have good := check_iff.mp h
  simp only [he, and_false, ↓reduceIte] at good
  obtain ⟨part, r, _, _, m⟩ := good
  exact ⟨(part.2 f hf).1, (part.2 f hf).2,
    fun x hx => part.1.mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, hx⟩),
    fun d hd => by rw [m f hf d hd]; rfl⟩

/-- The exact-cover enumerator admits every nonempty certified face. -/
theorem admissible_of_check {n edges fs f} (he : edges ≠ []) (h : check n edges fs = true)
    (hf : f ∈ fs) : Walks.Admissible («universe» edges) f := by
  obtain ⟨ne, nd, sub, next⟩ := check_face he h hf
  exact ⟨ne, nd, sub, Walks.chain_of_next nd next⟩

/-- The order in which a cover lists its faces does not affect acceptance. -/
theorem check_perm {n edges xs ys} (p : xs.Perm ys) (h : check n edges xs = true) :
    check n edges ys = true := by
  rw [check_iff] at h ⊢
  by_cases iso : n = 1 ∧ edges = [] <;> simp only [iso, ↓reduceIte] at h ⊢
  · subst xs
    exact List.perm_singleton.mp p.symm
  · obtain ⟨part, r, legal, nd, m⟩ := h
    exact ⟨⟨p.flatten.symm.trans part.1, fun f hf => part.2 f (p.mem_iff.mpr hf)⟩,
      r, legal, nd, fun f hf => m f (p.mem_iff.mpr hf)⟩

/-- A cyclic change of starting dart in a face preserves the verifier result. -/
theorem check_rotate {n edges fs f g} (p : f.IsRotated g) (h : check n edges (f :: fs) = true) :
    check n edges (g :: fs) = true := by
  rw [check_iff] at h ⊢
  by_cases iso : n = 1 ∧ edges = [] <;> simp only [iso, ↓reduceIte] at h ⊢
  · obtain ⟨rfl, rfl⟩ := List.cons.inj h
    exact congrArg (· :: []) (List.perm_nil.mp p.perm.symm)
  · obtain ⟨part, r, legal, nd, m⟩ := h
    have hf := part.2 f (.head _)
    have hg : g ≠ [] ∧ g.Nodup :=
      ⟨fun e => hf.1 (List.perm_nil.mp (e ▸ p.perm)), p.nodup_iff.mp hf.2⟩
    refine ⟨⟨(p.perm.symm.append_right fs.flatten).trans part.1, ?_⟩, r, legal, nd, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hg
      · exact part.2 w (.tail _ hw)
    · intro w hw d hd
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [← List.formPerm_eq_of_isRotated hf.2 p]
        exact m _ (.head _) d (p.mem_iff.mpr hd)
      · exact m w (.tail _ hw) d hd

/-- A legal row system contains exactly the darts of the input. -/
theorem dart_iff {n edges r} (hr : Legal n edges r) (G : SimpleInput n edges) (d : Edge) :
    d ∈ darts r ↔ d ∈ «universe» edges := by
  rcases d with ⟨u, v⟩
  rw [mem_darts, mem_universe]
  constructor
  · rintro ⟨hu, hv⟩
    exact mem_neighbors.mp ((hr.2 u (hr.1 ▸ hu)).mem_iff.mp hv)
  · intro hd
    have hv := mem_neighbors.mpr hd
    have hu := G.neighbor_lt (mem_neighbors.mpr hd.symm)
    exact ⟨hr.1 ▸ hu, (hr.2 u hu).mem_iff.mpr hv⟩

/-- The darts in a certified face are exactly the bounded walk computed from any of its darts. -/
theorem faceWalk_eq {r fs f} (valid : Valid r) (m : Matches r fs) (hf : f ∈ fs) (nd : f.Nodup)
    (x : Dart r) (hx : x.val ∈ f) : faceWalk r x.val = f.toFinset := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  let p := facePerm valid
  have walk (k : Nat) : ((p ^ k) x).val = f[(i + k) % f.length]'(Nat.mod_lt _ (by omega)) := by
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt hi] using hix.symm
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change faceStep r _ = _
      have hm : ((p ^ k) x).val ∈ f := ih ▸ List.getElem_mem _
      rw [← m f hf _ hm, ih, List.formPerm_apply_getElem _ nd]
      simp [Nat.add_assoc]
  ext z
  rw [List.mem_toFinset, mem_faceWalk valid]
  constructor
  · rintro ⟨y, rfl, same⟩
    obtain ⟨k, hk⟩ := same.exists_nat_pow_eq
    change (p ^ k) x = y at hk
    rw [← hk, walk]
    exact List.getElem_mem _
  · intro hz
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
    let k := f.length - i + j
    refine ⟨(p ^ k) x, ?_, ⟨k, by rw [zpow_natCast]⟩⟩
    have add : i + k = f.length + j := by dsimp [k]; omega
    simp only [walk, add, Nat.add_mod_left, Nat.mod_eq_of_lt hj]

/-- A matching partition counts the dart orbits of the specified rotation. -/
theorem orbitCount_partition {n edges fs r} (G : SimpleInput n edges)
    (part : Partition edges fs) (legal : Legal n edges r) (m : Matches r fs) :
    orbitCount r = fs.length := by
  let keys := fs.map List.toFinset
  have nd := part.1.nodup_iff.mpr (universe_nodup G)
  have disj := (List.pairwise_flatten.mp nd).2
  have distinct : keys.Nodup := by
    apply List.pairwise_map.mpr
    apply disj.imp_of_mem
    intro f g hf _ sep eq
    obtain ⟨d, hd⟩ := f.exists_mem_of_ne_nil (part.2 f hf).1
    have same : f.toFinset = g.toFinset := eq
    have mem : d ∈ g.toFinset := same ▸ List.mem_toFinset.mpr hd
    exact sep _ hd _ (List.mem_toFinset.mp mem) rfl
  have equal : (darts r).image (faceWalk r) = keys.toFinset := by
    ext s
    simp only [keys, Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have cover := part.1.mem_iff.mpr ((dart_iff legal G d).mp hd)
      obtain ⟨f, hf, hdf⟩ := List.mem_flatten.mp cover
      exact ⟨f, hf, (faceWalk_eq (valid_of_legal G legal) m hf (part.2 f hf).2 ⟨d, hd⟩ hdf).symm⟩
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨d, hd⟩ := f.exists_mem_of_ne_nil (part.2 f hf).1
      have mem := (dart_iff legal G d).mpr (part.1.mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, hd⟩))
      exact ⟨d, mem, faceWalk_eq (valid_of_legal G legal) m hf (part.2 f hf).2 ⟨d, mem⟩ hd⟩
  rw [orbitCount, equal, List.toFinset_card_of_nodup distinct]
  simp [keys]

private theorem isolated_iff {n edges r} (G : SimpleInput n edges) (legal : Legal n edges r) :
    r = [[]] ↔ n = 1 ∧ edges = [] := by
  constructor
  · rintro rfl
    have hn : n = 1 := legal.1.symm
    refine ⟨hn, List.eq_nil_iff_forall_not_mem.mpr ?_⟩
    intro e he
    have := G.ordered e he
    have := G.bounded e he
    omega
  · rintro ⟨rfl, rfl⟩
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_pos (by rw [legal.1]; decide)
    have nil : xs = [] := by have := legal.1; simpa using this
    subst xs
    have eq := legal.2 0 (by decide)
    simpa [neighbors] using eq

/-- Every listed turn is the face step of the rows returned by the verifier. -/
theorem matches_readRows {n edges fs} (h : check n edges fs = true) :
    Matches (readRows n edges fs) fs := by
  unfold check at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst fs
    simp [Matches]
  · exact (ordinary_iff.mp h).2.2.2

/-- The recovered rows are a legal witness with exactly the certified face count. -/
theorem readRows_of_check {n edges fs} (G : SimpleInput n edges) (h : check n edges fs = true) :
    Legal n edges (readRows n edges fs) ∧ faceCount (readRows n edges fs) = fs.length := by
  unfold check at h
  split at h
  · rename_i hi
    obtain ⟨rfl, rfl⟩ := hi
    simp only [decide_eq_true_eq] at h
    subst fs
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    intro v hv
    have : v = 0 := by omega
    subst v
    exact .refl _
  · rename_i hi
    obtain ⟨part, legal, _, m⟩ := ordinary_iff.mp h
    refine ⟨legal, ?_⟩
    have ne : readRows n edges fs ≠ [[]] := fun e => hi ((isolated_iff G legal).mp e)
    simpa only [faceCount, ne, ↓reduceIte] using orbitCount_partition G part legal m

/-- Every accepted certificate has a legal rotation whose executable face count is its length. -/
theorem legal_of_check {n edges fs} (G : SimpleInput n edges) (h : check n edges fs = true) :
    ∃ r, Legal n edges r ∧ faceCount r = fs.length :=
  ⟨_, readRows_of_check G h⟩

/-- Every legal rotation admits a dart-word certificate with precisely its executable face count. -/
theorem exists_check_of_legal {n edges r} (G : SimpleInput n edges) (legal : Legal n edges r) :
    ∃ fs, check n edges fs = true ∧ fs.length = faceCount r := by
  by_cases iso : n = 1 ∧ edges = []
  · obtain ⟨rfl, rfl⟩ := iso
    exact ⟨[[]], check_isolated.mpr rfl, by rw [(isolated_iff G legal).mpr ⟨rfl, rfl⟩]; rfl⟩
  let p := facePerm (valid_of_legal G legal)
  let ws := OrbitWords.words p
  let fs := ws.map (List.map Subtype.val)
  have flat : fs.flatten = ws.flatten.map Subtype.val := List.map_flatten.symm
  have part : Partition edges fs := by
    constructor
    · rw [flat]
      apply List.perm_of_nodup_nodup_toFinset_eq
        ((OrbitWords.nodup_flatten_words p).map Subtype.val_injective) (universe_nodup G)
      ext d
      simp only [List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨x, _, rfl⟩
        exact (dart_iff legal G _).mp x.prop
      · intro hd
        let x : Dart r := ⟨d, (dart_iff legal G d).mpr hd⟩
        exact ⟨x, OrbitWords.mem_flatten_words p x, rfl⟩
    · intro f hf
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
      obtain ⟨c, rfl⟩ := (OrbitWords.mem_words p w).mp hw
      exact ⟨List.ne_nil_of_mem (List.mem_map_of_mem (f := Subtype.val)
        ((OrbitWords.mem_word p c.out c.out).mpr .rfl)),
        (OrbitWords.nodup_word p c.out).map Subtype.val_injective⟩
  have turns : Matches r fs := by
    intro f hf d hd
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
    obtain ⟨c, rfl⟩ := (OrbitWords.mem_words p w).mp hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    rw [OrbitWords.formPerm_map_apply _ Subtype.val_injective _ (OrbitWords.nodup_word ..) _ hx,
      OrbitWords.step_word p _ _ hx]
    rfl
  refine ⟨fs, check_iff.mpr (by simp only [iso, ↓reduceIte]; exact
    ⟨part, r, legal, fun v _ => (valid_of_legal G legal).nodup v, turns⟩), ?_⟩
  simpa only [faceCount, show r ≠ [[]] from fun h => iso ((isolated_iff G legal).mp h),
    ↓reduceIte] using (orbitCount_partition G part legal turns).symm

/-- Feasible numbers of certified faces coincide with the face counts of legal rotations. -/
theorem exists_check_iff_faces {n edges k} (G : SimpleInput n edges) :
    (∃ fs, check n edges fs = true ∧ fs.length = k) ↔ ∃ r, Legal n edges r ∧ faceCount r = k := by
  constructor
  · rintro ⟨fs, h, rfl⟩
    exact legal_of_check G h
  · rintro ⟨r, legal, rfl⟩
    exact exists_check_of_legal G legal

/-- An Euler genus is realizable exactly when it has a facial cover certificate. -/
theorem realizes_iff_check {n edges g} (G : SimpleInput n edges) :
    Realizes n edges g ↔ ∃ fs, check n edges fs = true ∧
      2 + edges.length = n + fs.length + 2 * g := by
  constructor
  · rintro ⟨r, legal, euler⟩
    obtain ⟨fs, h, he⟩ := exists_check_of_legal G legal
    exact ⟨fs, h, he ▸ euler⟩
  · rintro ⟨fs, h, euler⟩
    obtain ⟨r, legal, he⟩ := legal_of_check G h
    exact ⟨r, legal, he ▸ euler⟩

end Page.Certificate
