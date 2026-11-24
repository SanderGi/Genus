/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.Certificate

/-! # Pruning partial vertex rotations

At a vertex `v`, consecutive darts `(a,v), (v,b)` fix the successor of neighbor
`a` to be `b`. The length of any nonempty closed path of fixed successors in a
legal row is a multiple of the degree. On at most five incidences a complete
permutation with no fixed points or reciprocal turns has only one orbit.
-/

@[expose] public section

namespace Page.Turns

open MultiGenus MultiGenus.Faces MultiGenus.Rotations

/-- The two consecutive darts of a selected face prescribe a turn, including at wraparound. -/
def Recorded (chosen : List Certificate.Face) (v a b : Nat) : Prop :=
  ∃ f ∈ chosen, (a, v) ∈ f ∧ f.formPerm (a, v) = (v, b)

/-- Following exactly `k` already assigned successors. -/
inductive Path {α : Type*} (turn : α → α → Prop) : Nat → α → α → Prop where
  /-- Start at the given neighbor. -/
  | nil (a) : Path turn 0 a a
  /-- Follow one additional turn. -/
  | snoc {k a b c} : Path turn k a b → turn b c → Path turn (k + 1) a c

/-- A permutation extending all assigned turns follows each fixed path. -/
theorem Path.pow_apply {α : Type*} {turn : α → α → Prop} {k a b}
    (path : Path turn k a b) (p : Equiv.Perm α) (ext : ∀ x y, turn x y → p x = y) :
    (p ^ k) a = b := by
  induction path with
  | nil => rfl
  | snoc _ step ih => rw [pow_succ', Equiv.Perm.mul_apply, ih]; exact ext _ _ step

/-- Prepend one assigned turn to the path already present at a vertex. -/
theorem Path.cons {α : Type*} {turn : α → α → Prop} {k a b c}
    (step : turn a b) (path : Path turn k b c) : Path turn (k + 1) a c := by
  induction path with
  | nil => exact (Path.nil _).snoc step
  | snoc _ last ih => exact (ih step).snoc last

/-- Matching a completed set of faces extends every turn in any chosen subset. -/
theorem extends_recorded {r fs chosen v} (m : Certificate.Matches r fs) (sub : chosen ⊆ fs)
    {a b : Nat} (h : Recorded chosen v a b) : (row r v).formPerm a = b := by
  obtain ⟨f, hf, ha, next⟩ := h
  exact congrArg Prod.snd ((m f (sub hf) _ ha).symm.trans next)

/-- Any nonempty closed walk of fixed turns in a legal cyclic row has length divisible by
the degree. In particular, closing a proper component precludes extending those turns. -/
theorem length_dvd_of_closed {turn : Nat → Nat → Prop} {xs : List Nat} {k a : Nat}
    (nd : xs.Nodup) (ha : a ∈ xs) (ext : ∀ x y, turn x y → xs.formPerm x = y)
    (path : Path turn k a a) : xs.length ∣ k := by
  have cyc : xs.formPerm.IsCycleOn (xs.toFinset : Set Nat) := by
    simpa only [List.coe_toFinset] using nd.isCycleOn_formPerm
  simpa only [List.toFinset_card_of_nodup nd] using
    (cyc.pow_apply_eq (List.mem_toFinset.mpr ha)).mp (path.pow_apply _ ext)

/-- A nonempty set of neighbors with a fixed successor inside the set at each member
must contain every neighbor in any cyclic row extending those assignments. -/
theorem subset_of_closed_turns {xs : List Nat} {s : Set Nat} {turn : Nat → Nat → Prop}
    (nd : xs.Nodup) {a : Nat} (ha : a ∈ xs) (start : a ∈ s)
    (closed : ∀ x ∈ s, ∃ y ∈ s, turn x y)
    (ext : ∀ x y, turn x y → xs.formPerm x = y) : ∀ b ∈ xs, b ∈ s := by
  have cyc : xs.formPerm.IsCycleOn (xs.toFinset : Set Nat) := by
    simpa only [List.coe_toFinset] using nd.isCycleOn_formPerm
  have stays (k : Nat) : (xs.formPerm ^ k) a ∈ s := by
    induction k with
    | zero => exact start
    | succ k ih =>
      obtain ⟨y, hy, edge⟩ := closed _ ih
      rw [pow_succ', Equiv.Perm.mul_apply, ext _ _ edge]
      exact hy
  intro b hb
  obtain ⟨k, _, rfl⟩ := cyc.exists_pow_eq (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)
  exact stays k

/-- A newly fixed turn closing a component of smaller size than the degree cannot extend
to any legal neighbor row. The relation may include turns of a face still being generated. -/
theorem no_row_of_early_closure {ns : List Nat} {turn : Nat → Nat → Prop} {a b k}
    (ha : a ∈ ns) (path : Path turn k b a) (close : turn a b) (short : k + 1 < ns.length) :
    ¬ ∃ xs : List Nat, xs.Perm ns ∧ xs.Nodup ∧ ∀ x y, turn x y → xs.formPerm x = y := by
  rintro ⟨xs, perm, nd, ext⟩
  have dvd := length_dvd_of_closed nd (perm.mem_iff.mpr ha) ext (Path.cons close path)
  exact (Nat.not_le_of_gt short) (perm.length_eq ▸ Nat.le_of_dvd (by omega) dvd)

/-- A selected transition closing a path before the full degree rules out every accepted
certificate containing the selected faces. The new edge contributes one to the native span. -/
theorem check_false_of_early_closure {n edges chosen fs v a b k}
    (hv : v < n) (ha : a ∈ neighbors edges v)
    (path : Path (Recorded chosen v) k b a) (close : Recorded chosen v a b)
    (short : k + 1 < (neighbors edges v).length) (sub : chosen ⊆ fs) :
    Certificate.check n edges fs = false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  have cert := Certificate.check_iff.mp ok
  split at cert
  · rename_i iso
    obtain ⟨rfl, rfl⟩ := iso
    simp [neighbors] at ha
  · obtain ⟨_, r, legal, nd, m⟩ := cert
    exact no_row_of_early_closure ha path close short
      ⟨row r v, legal.2 v hv, nd v hv, fun _ _ h => extends_recorded m sub h⟩

/-- Two distinct orbits would contain six distinct incidences: the first three forward
iterates from each orbit. This justifies the short-cycle shortcut for degrees three to five. -/
theorem sameCycle_of_degree_le_five {D : Type*} [Fintype D] (p : Equiv.Perm D)
    (small : Fintype.card D ≤ 5) (noFixed : ∀ x, p x ≠ x) (noTwo : ∀ x, p (p x) ≠ x)
    (x y : D) : p.SameCycle x y := by
  classical
  by_contra apart
  let triple (z : D) := [z, p z, p (p z)]
  have nd (z : D) : (triple z).Nodup := by
    simp [triple, Ne.symm (noFixed z), Ne.symm (noTwo z), Ne.symm (noFixed (p z))]
  have same {a z : D} (h : a ∈ triple z) : p.SameCycle z a := by
    simp only [triple, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact .rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · exact Equiv.Perm.SameCycle.rfl.apply_right.apply_right
  have six : (triple x ++ triple y).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨nd x, nd y, fun _ hx _ hy eq => apart ((same hx).trans (eq ▸ (same hy).symm))⟩
  have bound := six.length_le_card
  simp only [triple, List.length_append, List.length_cons, List.length_nil] at bound
  omega

private theorem unique_face {fs : List Certificate.Face} {f g d}
    (nd : fs.flatten.Nodup) (hf : f ∈ fs) (hg : g ∈ fs) (df : d ∈ f) (dg : d ∈ g) :
    f = g := by
  by_contra ne
  have perm := List.perm_cons_erase hf
  have sep := (List.nodup_append.mp (perm.flatten.nodup_iff.mp nd)).2.2
  have hg' : g ∈ fs.erase f := (List.mem_cons.mp (perm.mem_iff.mp hg)).resolve_left (Ne.symm ne)
  exact sep _ df _ (List.mem_flatten.mpr ⟨g, hg', dg⟩) rfl

/-- The turns of a full dart partition of closed walks give a permutation on each neighbor
set, even before checking whether that permutation is a single cycle. -/
theorem exists_turnPerm {n edges fs} (G : SimpleInput n edges)
    (part : Certificate.Partition edges fs)
    (fits : ∀ f ∈ fs, ∀ d ∈ f, (f.formPerm d).1 = d.2) (v : Nat) :
    ∃ p : Equiv.Perm (neighbors edges v).toFinset,
      ∀ a b : (neighbors edges v).toFinset, Recorded fs v a b ↔ p a = b := by
  classical
  let N := (neighbors edges v).toFinset
  have nd := part.1.nodup_iff.mpr (Certificate.universe_nodup G)
  have total (a : N) : ∃ b : N, Recorded fs v a b := by
    have mem := Certificate.mem_universe.mpr (mem_neighbors.mp (List.mem_toFinset.mp a.2)).symm
    obtain ⟨f, hf, ha⟩ := List.mem_flatten.mp (part.1.mem_iff.mpr (mem : (a.val, v) ∈ _))
    let b := (f.formPerm (a.val, v)).2
    have next : f.formPerm (a.val, v) = (v, b) := Prod.ext (fits f hf _ ha) rfl
    have out : (v, b) ∈ f := next ▸ List.formPerm_mem_iff_mem.mpr ha
    have adj := Certificate.mem_universe.mp
        (part.1.mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, out⟩))
    exact ⟨⟨b, List.mem_toFinset.mpr (mem_neighbors.mpr adj)⟩, f, hf, ha, next⟩
  choose succ turn using total
  have bij : Function.Injective succ := by
    intro a b eq
    obtain ⟨f, hf, ha, ea⟩ := turn a
    obtain ⟨g, hg, hb, eb⟩ := turn b
    rw [← eq] at eb
    have out₁ := ea ▸ List.formPerm_mem_iff_mem.mpr ha
    have out₂ := eb ▸ List.formPerm_mem_iff_mem.mpr hb
    obtain rfl := unique_face nd hf hg out₁ out₂
    exact Subtype.ext (congrArg Prod.fst (f.formPerm.injective (ea.trans eb.symm)))
  refine ⟨Equiv.ofBijective succ ⟨bij, Finite.injective_iff_surjective.mp bij⟩, ?_⟩
  intro a b
  constructor
  · rintro ⟨f, hf, ha, ea⟩
    obtain ⟨g, hg, hb, eb⟩ := turn a
    obtain rfl := unique_face nd hf hg ha hb
    exact Subtype.ext (congrArg Prod.snd (eb.symm.trans ea))
  · rintro rfl
    exact turn a

private theorem sameCycle_small {D : Type*} [Fintype D] (p : Equiv.Perm D)
    (small : Fintype.card D ≤ 5) (nofix : 1 < Fintype.card D → ∀ x, p x ≠ x)
    (notwo : 2 < Fintype.card D → ∀ x, p (p x) ≠ x) (x y : D) : p.SameCycle x y := by
  classical
  by_cases h : 2 < Fintype.card D
  · exact sameCycle_of_degree_le_five p small (nofix (by omega)) (notwo h) x y
  by_cases h₁ : 1 < Fintype.card D
  · by_contra apart
    have hx : x ≠ y := fun e => apart (e ▸ Equiv.Perm.SameCycle.rfl)
    have hpx : p x ≠ y := fun e => apart (e ▸ Equiv.Perm.SameCycle.rfl.apply_right)
    have nd : [x, p x, y].Nodup := by simp [hx, hpx, Ne.symm (nofix h₁ x)]
    have bound := nd.length_le_card
    simp only [List.length_cons, List.length_nil] at bound
    omega
  · have : Subsingleton D := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    rw [Subsingleton.elim x y]

private theorem row_of_one_cycle {ns : List Nat} (nd : ns.Nodup)
    (p : Equiv.Perm ns.toFinset) (single : ∀ x y, p.SameCycle x y) :
    ∃ xs : List Nat, xs.Perm ns ∧ ∀ a : ns.toFinset, xs.formPerm a.val = (p a).val := by
  classical
  cases ns with
  | nil => exact ⟨[], .refl _, fun a => by simpa using a.2⟩
  | cons u us =>
    let base : (u :: us).toFinset := ⟨u, by simp⟩
    let w := OrbitWords.word p base
    have allMem (a : (u :: us).toFinset) : a ∈ w := (OrbitWords.mem_word ..).mpr (single _ _)
    have wnd : w.Nodup := OrbitWords.nodup_word ..
    refine ⟨w.map Subtype.val, List.perm_of_nodup_nodup_toFinset_eq
      (wnd.map Subtype.val_injective) nd ?_, ?_⟩
    · ext a
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨fun ⟨x, _, h⟩ => h ▸ List.mem_toFinset.mp x.2,
        fun h => ⟨⟨a, List.mem_toFinset.mpr h⟩, allMem _, rfl⟩⟩
    · intro a
      rw [OrbitWords.formPerm_map_apply _ Subtype.val_injective _ wnd _ (allMem a)]
      exact congrArg Subtype.val (OrbitWords.step_word _ _ _ (allMem a))

/-- The native short-turn tests allow a fixed point at a leaf and a reciprocal pair at
degree two. At larger degrees each would close a proper cycle. -/
def NoShortTurns (edges : List Edge) (fs : List Certificate.Face) : Prop :=
  ∀ v a, (1 < (neighbors edges v).length → ¬ Recorded fs v a a) ∧
    (2 < (neighbors edges v).length → ∀ b, Recorded fs v a b → ¬ Recorded fs v b a)

private theorem neighbor_of_recorded {edges fs v a b} (part : Certificate.Partition edges fs)
    (rec : Recorded fs v a b) : a ∈ neighbors edges v := by
  obtain ⟨f, hf, ha, _⟩ := rec
  exact mem_neighbors.mpr (Certificate.mem_universe.mp
    (part.1.mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, ha⟩))).symm

/-- For a partition into closed dart words on a graph of maximum degree five, the two local
turn tests characterize verification. The partition itself supplies the local bijections. -/
theorem check_iff_noShortTurns {n edges fs} (G : SimpleInput n edges) (he : edges ≠ [])
    (small : ∀ v < n, (neighbors edges v).length ≤ 5) (part : Certificate.Partition edges fs)
    (fits : ∀ f ∈ fs, ∀ d ∈ f, (f.formPerm d).1 = d.2) :
    Certificate.check n edges fs = true ↔ NoShortTurns edges fs := by
  constructor
  · intro ok v a
    have bounded {a b} (rec : Recorded fs v a b) : v < n :=
      G.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp (neighbor_of_recorded part rec)).symm)
    constructor
    · intro deg rec
      have bad := check_false_of_early_closure (bounded rec) (neighbor_of_recorded part rec)
        (.nil a) rec deg (List.Subset.refl fs)
      simp [ok] at bad
    · intro deg b ab ba
      have bad := check_false_of_early_closure (bounded ab) (neighbor_of_recorded part ab)
        ((Path.nil b).snoc ba) ab deg (List.Subset.refl fs)
      simp [ok] at bad
  · intro short
    classical
    have localRow (v : Fin n) : ∃ xs : List Nat, xs.Perm (neighbors edges v) ∧
        ∀ a b, Recorded fs v a b → xs.formPerm a = b := by
      let N := (neighbors edges v).toFinset
      obtain ⟨p, turns⟩ := exists_turnPerm G part fits v
      have card : Fintype.card N = (neighbors edges v).length := by
        exact (Fintype.card_coe N).trans (List.toFinset_card_of_nodup (G.neighbors_nodup v))
      have forward (a : N) := (turns a (p a)).mpr rfl
      have single := sameCycle_small p (card ▸ small v v.isLt)
        (fun h a eq => (short v a).1 (card ▸ h) ((turns a a).mpr eq))
        (fun h a eq => (short v a).2 (card ▸ h) (p a) (forward a) ((turns (p a) a).mpr eq))
      obtain ⟨xs, perm, step⟩ := row_of_one_cycle (G.neighbors_nodup v) p single
      refine ⟨xs, perm, ?_⟩
      intro a b ab
      let x : N := ⟨a, List.mem_toFinset.mpr (neighbor_of_recorded part ab)⟩
      obtain ⟨f, hf, ha, e⟩ := ab
      have out : (v.val, b) ∈ f := e ▸ List.formPerm_mem_iff_mem.mpr ha
      have adj := Certificate.mem_universe.mp
        (part.1.mem_iff.mp (List.mem_flatten.mpr ⟨f, hf, out⟩))
      let y : N := ⟨b, List.mem_toFinset.mpr (mem_neighbors.mpr adj)⟩
      exact (step x).trans (congrArg Subtype.val ((turns x y).mp ⟨f, hf, ha, e⟩))
    choose xs perm step using localRow
    let r := List.ofFn xs
    have get (v : Nat) (hv : v < n) : row r v = xs ⟨v, hv⟩ := by
      simp [row, r, List.getD_eq_getElem?_getD, hv]
    apply Certificate.check_iff.mpr
    simp only [he, and_false, ↓reduceIte]
    refine ⟨part, r, ⟨by simp [r], ?_⟩, ?_, ?_⟩
    · intro v hv
      change (row r v).Perm _
      rw [get v hv]
      exact perm ⟨v, hv⟩
    · intro v hv
      rw [get v hv]
      exact (perm ⟨v, hv⟩).nodup_iff.mpr (G.neighbors_nodup v)
    intro f hf d hd
    have eq := fits f hf d hd
    have turn : Recorded fs d.2 d.1 (f.formPerm d).2 := ⟨f, hf, hd, Prod.ext eq rfl⟩
    have adj := neighbor_of_recorded part turn
    have hv := G.neighbor_lt (mem_neighbors.mpr (mem_neighbors.mp adj).symm)
    apply Prod.ext eq
    change _ = (row r _).formPerm _
    rw [get _ hv]
    exact (step ⟨_, hv⟩ _ _ turn).symm

end Page.Turns
