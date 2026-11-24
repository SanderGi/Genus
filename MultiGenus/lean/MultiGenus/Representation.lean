/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Reduction
public import MultiGenus.Search
import Mathlib.Data.List.FinRange

/-! # Representing arbitrary dart rotations by neighbor rows

One orbit of the vertex permutation at a time, read off its destination labels up
to the first return. Its minimal period supplies both the row length and the
wraparound step. Period one gives the singleton row at a leaf.
-/

public section

namespace MultiGenus.Representation

open Rotations Faces Reduction Surgery Equiv Equiv.Perm Function

private theorem fiberRow {rows : Rows} (valid : Valid rows) (p : Perm (Dart rows))
    (hp : Ordered (fun d : Dart rows => d.val.1) p) (x : Dart rows) :
    ∃ l : List Nat, l.Perm (row rows x.val.1) ∧
      ∀ d : Dart rows, d.val.1 = x.val.1 → l.formPerm d.val.2 = (p d).val.2 := by
  classical
  let t := minimalPeriod p x
  have pos : 0 < t := minimalPeriod_pos_of_mem_periodicPts
    (by rw [injective_iff_periodicPts_eq_univ.mp p.injective]; exact Set.mem_univ _)
  let visit (i : Fin t) := p^[i.val] x
  let dest (i : Fin t) := (visit i).val.2
  have origin (i : Fin t) : (visit i).val.1 = x.val.1 := (hp _ _ |>.mp
    (show p.SameCycle x (visit i) from ⟨(i.val : ℤ), by simp [visit, coe_pow]⟩)).symm
  have onto (d : Dart rows) (hd : d.val.1 = x.val.1) : ∃ i, visit i = d := by
    obtain ⟨m, hm⟩ := ((hp x d).mpr hd.symm).exists_nat_pow_eq
    refine ⟨⟨m % t, Nat.mod_lt _ pos⟩, ?_⟩
    exact (iterate_mod_minimalPeriod_eq (f := p) (x := x) (n := m)).trans
      (by simpa [coe_pow] using hm)
  have inj : Injective dest := by
    intro i j eq
    exact Fin.ext (iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
      (Subtype.ext (Prod.ext ((origin i).trans (origin j).symm) eq) : visit i = visit j))
  let l := List.ofFn dest
  have nd : l.Nodup := List.nodup_ofFn.mpr inj
  refine ⟨l, (List.perm_ext_iff_of_nodup nd (valid.nodup _)).mpr ?_, ?_⟩
  · intro v
    constructor
    · rintro hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact origin i ▸ (mem_darts.mp (visit i).prop).2
    · intro hv
      let d : Dart rows := ⟨(x.val.1, v), mem_darts.mpr ⟨(mem_darts.mp x.prop).1, hv⟩⟩
      obtain ⟨i, hi⟩ := onto d rfl
      exact List.mem_ofFn.mpr ⟨i, congrArg (fun z : Dart rows => z.val.2) hi⟩
  · intro d hd
    obtain ⟨i, rfl⟩ := onto d hd
    have len : l.length = t := List.length_ofFn ..
    have hi : i.val < l.length := by rw [len]; exact i.isLt
    have val : l[i.val] = dest i := List.getElem_ofFn hi
    rw [← show dest i = (visit i).val.2 from rfl, ← val, List.formPerm_apply_getElem _ nd _ hi]
    simp only [l, List.length_ofFn, List.getElem_ofFn]
    apply congrArg (fun d : Dart rows => d.val.2)
    exact (iterate_mod_minimalPeriod_eq (f := p) (x := x) (n := i.val + 1)).trans
      (iterate_succ_apply' ..)

/-- A cyclic ordering of each dart fiber is represented by legal rows whose successor at
every neighbor is exactly the prescribed outgoing dart. -/
theorem exists_rows_of_ordered {n : Nat} {edges : List Edge} {rows : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rows)
    (hn : 1 < n) (p : Perm (Dart rows)) (hp : Ordered (fun d : Dart rows => d.val.1) p) :
    ∃ result, Legal n edges result ∧ ∀ d : Dart rows,
      (row result d.val.1).formPerm d.val.2 = (p d).val.2 := by
  classical
  have each (i : Fin n) : ∃ l : List Nat, l.Perm (neighbors edges i.val) ∧
      ∀ d : Dart rows, d.val.1 = i.val → l.formPerm d.val.2 = (p d).val.2 := by
    obtain ⟨x, hx⟩ := Map.origin_surjective hr con hn i
    have he : x.val.1 = i.val := congrArg Fin.val hx
    obtain ⟨l, hl, hstep⟩ := fiberRow (valid_of_legal G hr) p hp x
    rw [he] at hl hstep
    exact ⟨l, hl.trans (hr.2 i.val i.isLt), hstep⟩
  choose f hf hs using each
  have row_eq (i : Fin n) : row (List.ofFn f) i.val = f i := by
    simp [row, List.getD_eq_getElem?_getD, i.isLt]
  have legal : Legal n edges (List.ofFn f) := by
    refine ⟨List.length_ofFn, fun v hv => ?_⟩
    change (row (List.ofFn f) v).Perm _
    rw [row_eq ⟨v, hv⟩]
    exact hf _
  refine ⟨List.ofFn f, legal, ?_⟩
  intro d
  let i : Fin n := ⟨d.val.1, hr.1 ▸ (mem_darts.mp d.prop).1⟩
  rw [row_eq i]
  exact hs i d rfl

private theorem dart_mem_iff {n : Nat} {edges : List Edge} {rs ss : Rows} (hr : Legal n edges rs)
    (hs : Legal n edges ss) (d : Edge) : d ∈ darts rs ↔ d ∈ darts ss := by
  obtain ⟨u, v⟩ := d
  simp only [mem_darts, hr.1, hs.1]
  exact and_congr_right fun hu => (hr.2 u hu).mem_iff.trans (hs.2 u hu).mem_iff.symm

private def rename {n : Nat} {edges : List Edge} {rs ss : Rows} (hr : Legal n edges rs)
    (hs : Legal n edges ss) : Dart rs ≃ Dart ss :=
  Equiv.subtypeEquivRight (dart_mem_iff hr hs)

private theorem count_faces {n : Nat} {edges : List Edge} {rs : Rows}
    (hr : Legal n edges rs) (hn : 1 < n) (valid : Valid rs) :
    countCycles (rho rs * alpha valid) = faceCount rs := by
  have many : rs ≠ [[]] := by intro he; have := hr.1; simp_all
  simpa only [many, ite_false, countCycles, facePerm] using (faceCount_eq valid).symm

/-- Transporting a rotation through a bijection preserving dart origins and reversal preserves
its Euler equation. Vertex names are allowed to differ by an equivalence as well. -/
theorem attains_of_equiv {D E V W : Type*} [Finite D] [Finite E] {v m g : Nat}
    {t : D → V} {s : E → W} {r : Perm D} {q : Perm E} (e : D ≃ E)
    (vertex : ∀ x y, t x = t y ↔ s (e x) = s (e y)) (reverse : ∀ x, e (r x) = q (e x))
    (h : Attains v m t r g) : Attains v m s q g := by
  obtain ⟨p, hp, he⟩ := h
  let f := e.permCongr p
  have step (x : D) : e (p x) = f (e x) := by simp [f, Equiv.permCongr_apply]
  have back (x : E) : e.symm (f x) = p (e.symm x) := by
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← step, e.symm_apply_apply, e.symm_apply_apply]
  have ord : Ordered s f := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← vertex, ← hp]
    constructor
    · intro h
      simpa only [e.symm_apply_apply] using
        map_sameCycle f p e.symm (fun z => by rw [back]; exact SameCycle.rfl.apply_right) h
    · exact map_sameCycle p f e (fun z => by rw [step]; exact SameCycle.rfl.apply_right)
  refine ⟨f, ord, ?_⟩
  rwa [← countCycles_congr e (p * r) (f * q) (fun x => by
    change e (p (r x)) = f (q (e x))
    rw [step, reverse])]

/-- The dart spectrum of any legal presentation of the connected graph is exactly the
row-based genus spectrum used by the public search. -/
theorem attains_iff_realizes {n : Nat} {edges : List Edge} {rs : Rows} (G : SimpleInput n edges)
    (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n) (g : Nat) :
    Attains n edges.length (fun d : Dart rs => d.val.1) (alpha (valid_of_legal G hr)) g ↔
      Realizes n edges g := by
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨ss, hs, hstep⟩ := exists_rows_of_ordered G con hr hn p hp
    let e := rename hr hs
    have track (x : Dart rs) :
        e ((p * alpha (valid_of_legal G hr)) x) = (rho ss * alpha (valid_of_legal G hs)) (e x) := by
      let d := alpha (valid_of_legal G hr) x
      apply Subtype.ext
      exact Prod.ext (((hp d (p d)).mp SameCycle.rfl.apply_right).symm) (hstep d).symm
    rw [countCycles_congr e _ _ track, count_faces hs hn] at he
    exact ⟨ss, hs, he⟩
  · rintro ⟨ss, hs, he⟩
    apply attains_of_equiv (rename hs hr) (fun _ _ => Iff.rfl) (fun _ => Subtype.ext rfl)
      (t := fun d : Dart ss => d.val.1) (r := alpha (valid_of_legal G hs))
    exact ⟨rho ss, rho_sameCycle_iff (valid_of_legal G hs), by rwa [count_faces hs hn]⟩

/-- Inserting a leaf leaves exactly the genus values realized by the public row search. -/
theorem leaf_attains_iff_realizes {n : Nat} {edges : List Edge} {rs : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n)
    (a : Dart rs) (g : Nat) :
    Attains (n + 1) (edges.length + 1) (leafTail (fun d : Dart rs => d.val.1) a.val.1)
      (pairPerm (alpha (valid_of_legal G hr))) g ↔ Realizes n edges g :=
  (leaf_attains_iff n edges.length _ _ a g).trans (attains_iff_realizes G con hr hn g)

private theorem distinct_ends {n : Nat} {edges : List Edge} {rs : Rows} (G : SimpleInput n edges)
    (hr : Legal n edges rs) (a : Dart rs) : a.val.1 ≠ a.val.2 := by
  have mem := mem_darts.mp a.prop
  have hm := (hr.2 a.val.1 (hr.1 ▸ mem.1)).mem_iff.mp mem.2
  rcases mem_neighbors.mp hm with he | he
  · exact (G.ordered _ he).ne
  · exact (G.ordered _ he).ne'

/-- Subdividing an input edge preserves the public row-search genus spectrum. -/
theorem subdiv_attains_iff_realizes {n : Nat} {edges : List Edge} {rs : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n)
    (a : Dart rs) (g : Nat) :
    Attains (n + 1) (edges.length + 1) (subdivTail (fun d : Dart rs => d.val.1))
      (subdivReverse (alpha (valid_of_legal G hr)) (alpha (valid_of_legal G hr) a)) g ↔
      Realizes n edges g := by
  have ne : a ≠ alpha (valid_of_legal G hr) a := fun eq =>
    distinct_ends G hr a (congrArg (fun d : Dart rs => d.val.1) eq)
  exact (subdiv_attains_iff n edges.length _ _ ne rfl (Subtype.ext rfl) g).trans
    (attains_iff_realizes G con hr hn g)

/-- The executable minimum is also the least genus over all vertex permutations on the
fixed concrete dart set. -/
theorem minimumGenus_isLeast_attains {n : Nat} {edges : List Edge} {rs : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n) :
    IsLeast {g | Attains n edges.length (fun d : Dart rs => d.val.1)
      (alpha (valid_of_legal G hr)) g} (minimumGenus n edges) := by
  simpa only [attains_iff_realizes G con hr hn] using minimumGenus_isLeast G con

/-- A target genus bounds the public optimum exactly when the dart model of the graph with
the parallel two-edge path admits a rotation under that target. -/
theorem triangle_cutoff_iff {n : Nat} {edges : List Edge} {rs : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n)
    (a : Dart rs) (target : Nat) :
    (∃ g ≤ target, Attains (n + 1) (edges.length + 2)
      (triangleTail (fun d : Dart rs => d.val.1) a.val.1 a.val.2)
      (triangleReverse (alpha (valid_of_legal G hr))) g) ↔ minimumGenus n edges ≤ target := by
  have cut := triangle_atMost_iff n edges.length (fun d : Dart rs => d.val.1)
    (alpha (valid_of_legal G hr)) a (distinct_ends G hr a) (eulerExact_darts G con hr hn) target
  refine cut.trans ?_
  have least := minimumGenus_isLeast_attains G con hr hn
  exact ⟨fun ⟨g, hg, h⟩ => (least.2 h).trans hg, fun h => ⟨_, h, least.1⟩⟩

/-- Compare the two public optima when an input presents the enlarged parallel two-edge path.
The dart identification specifies the incidence fibers and actual reversal in that presentation. -/
theorem triangle_minimumGenus_eq {n : Nat} {edges more : List Edge} {rs ss : Rows}
    (G : SimpleInput n edges) (con : ConnectedInput n edges) (hr : Legal n edges rs) (hn : 1 < n)
    (H : SimpleInput (n + 1) more) (con' : ConnectedInput (n + 1) more)
    (hs : Legal (n + 1) more ss) (length_eq : more.length = edges.length + 2) (a : Dart rs)
    (e : Added (Added (Dart rs)) ≃ Dart ss)
    (origins : ∀ x y,
      triangleTail (fun d : Dart rs => d.val.1) a.val.1 a.val.2 x =
        triangleTail (fun d : Dart rs => d.val.1) a.val.1 a.val.2 y ↔
      (e x).val.1 = (e y).val.1)
    (reverse : ∀ x, e (triangleReverse (alpha (valid_of_legal G hr)) x) =
      alpha (valid_of_legal H hs) (e x)) :
    minimumGenus (n + 1) more = minimumGenus n edges := by
  have least := minimumGenus_isLeast_attains H con' hs (by omega)
  have cut (k : Nat) : minimumGenus (n + 1) more ≤ k ↔ minimumGenus n edges ≤ k := by
    rw [← triangle_cutoff_iff G con hr hn a k]
    constructor
    · intro hk
      refine ⟨_, hk, ?_⟩
      have h := least.1
      change Attains (n + 1) more.length _ _ _ at h
      rw [length_eq] at h
      apply attains_of_equiv e.symm _ _ h
      · intro u w
        simpa using (origins (e.symm u) (e.symm w)).symm
      · intro u
        apply e.injective
        simp [reverse]
    · rintro ⟨g, hg, h⟩
      have h' := attains_of_equiv (s := fun d : Dart ss => d.val.1) e origins reverse h
      rw [← length_eq] at h'
      exact (least.2 h').trans hg
  exact le_antisymm ((cut _).mpr le_rfl) ((cut _).mp le_rfl)

end MultiGenus.Representation
