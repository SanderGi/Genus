/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import MultiGenus.Darts
public import MultiGenus.Slots
public import MultiGenus.Surgery

/-! # Face changes under a concrete rotation extension

An insertion slot determines the old outgoing dart immediately after the new dart.
Naming these two old darts identifies the enlarged face permutation with edge surgery.
-/

public section

namespace MultiGenus.Extension

open Rotations Faces Equiv Equiv.Perm

variable {n : Nat} {pre : List Edge} {rows rows' : Rows} {u v : Nat}

/-- An edge prefix of a simple graph inherits simplicity and vertex bounds. -/
theorem simple_prefix {rest : List Edge} (G : SimpleInput n (pre ++ rest)) :
    SimpleInput n pre :=
  ⟨fun d hd => G.ordered d (List.mem_append_left _ hd),
   fun d hd => G.bounded d (List.mem_append_left _ hd), (List.nodup_append.mp G.nodup).1⟩

private theorem dart_iff {es : List Edge} (G : SimpleInput n es) (h : Legal n es rows)
    (x : Edge) : x ∈ darts rows ↔ x ∈ es ∨ x.swap ∈ es := by
  obtain ⟨a, b⟩ := x
  rw [mem_darts, h.1]
  constructor
  · exact fun ⟨ha, hb⟩ => mem_neighbors.mp ((h.2 a ha).mem_iff.mp hb)
  · intro hm
    have hb := mem_neighbors.mpr hm
    have ha := G.neighbor_lt (mem_neighbors.mpr hm.symm)
    exact ⟨ha, (h.2 a ha).mem_iff.mpr hb⟩

private def nameDart (e : Edge) : Dart rows ⊕ Bool → Edge
  | .inl x => x.val
  | .inr false => e
  | .inr true => e.swap

private noncomputable def extendDarts (e : Edge) (hne : e ≠ e.swap)
    (fresh : e ∉ darts rows) (fresh' : e.swap ∉ darts rows)
    (members : ∀ x, x ∈ darts rows' ↔ x ∈ darts rows ∨ x = e ∨ x = e.swap) :
    (Dart rows ⊕ Bool) ≃ Dart rows' := by
  let f (x : Dart rows ⊕ Bool) : Dart rows' := ⟨nameDart e x, (members _).2 (by
    rcases x with x | tag
    · exact Or.inl x.prop
    · cases tag
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl))⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    have he : nameDart e x = nameDart e y := congrArg Subtype.val eq
    rcases x with x | t <;> rcases y with y | s
    · exact congrArg Sum.inl (Subtype.ext he)
    · cases s <;> simp only [nameDart] at he
      · exact (fresh (he ▸ x.prop)).elim
      · exact (fresh' (he ▸ x.prop)).elim
    · cases t <;> simp only [nameDart] at he
      · exact (fresh (he.symm ▸ y.prop)).elim
      · exact (fresh' (he.symm ▸ y.prop)).elim
    · cases t <;> cases s
      · rfl
      · exact (hne he).elim
      · exact (hne he.symm).elim
      · rfl
  · intro y
    rcases (members _).1 y.prop with h | h | h
    · exact ⟨.inl ⟨_, h⟩, Subtype.ext rfl⟩
    · exact ⟨.inr false, Subtype.ext h.symm⟩
    · exact ⟨.inr true, Subtype.ext h.symm⟩

private theorem old_step (h : Valid rows) {k j : Nat} (ne : u ≠ v)
    (hu : (row rows' u).formPerm = swap v k * (row rows u).formPerm)
    (hv : (row rows' v).formPerm = swap u j * (row rows v).formPerm)
    (hout : ∀ w, w ≠ u → w ≠ v → row rows' w = row rows w)
    (fresh : v ∉ row rows u) (fresh' : u ∉ row rows v) (x : Dart rows) :
    faceStep rows' x.val =
      if faceStep rows x.val = (u, k) then (u, v)
      else if faceStep rows x.val = (v, j) then (v, u) else faceStep rows x.val := by
  obtain ⟨⟨a, b⟩, hx⟩ := x
  have hm := List.formPerm_apply_mem_of_mem (h.symmetric (mem_darts.mp hx).2)
  change (b, (row rows' b).formPerm a) = _
  by_cases bu : b = u
  · subst b
    have hnv : (row rows u).formPerm a ≠ v := fun eq => fresh (eq ▸ hm)
    simp [faceStep, hu, mul_apply, swap_apply_def, hnv, ne, apply_ite (Prod.mk u)]
  by_cases bv : b = v
  · subst b
    have hnu : (row rows v).formPerm a ≠ u := fun eq => fresh' (eq ▸ hm)
    simp [faceStep, hv, mul_apply, swap_apply_def, hnu, bu, apply_ite (Prod.mk v)]
  · simp [faceStep, hout b bu bv, bu, bv]

private theorem face_counts (h : Valid rows) (h' : Valid rows')
    (huv : u ≠ v) (fu : (u, v) ∉ darts rows) (fv : (v, u) ∉ darts rows)
    (mem : ∀ x, x ∈ darts rows' ↔ x ∈ darts rows ∨ x = (u, v) ∨ x = (v, u))
    {k j : Nat} (hk : (u, k) ∈ darts rows) (hj : (v, j) ∈ darts rows)
    (hu : (row rows' u).formPerm = swap v k * (row rows u).formPerm)
    (hv : (row rows' v).formPerm = swap u j * (row rows v).formPerm)
    (hout : ∀ w, w ≠ u → w ≠ v → row rows' w = row rows w) :
    Surgery.countCycles (facePerm h') = Surgery.countCycles
      (Surgery.insertEdge (facePerm h) (⟨(u, k), hk⟩ : Dart rows) ⟨(v, j), hj⟩) := by
  let a : Dart rows := ⟨(u, k), hk⟩
  let b : Dart rows := ⟨(v, j), hj⟩
  have ab : a ≠ b := fun eq => huv (congrArg (fun d : Dart rows => d.val.1) eq)
  have distinct : (u, v) ≠ (v, u) := fun eq => huv (congrArg Prod.fst eq)
  let E := extendDarts (u, v) distinct fu fv mem
  have valE (x) : (E x).val = nameDart (u, v) x := rfl
  have fresh : v ∉ row rows u := fun hm => fu (mem_darts.mpr ⟨(mem_darts.mp hk).1, hm⟩)
  have fresh' : u ∉ row rows v := fun hm => fv (mem_darts.mpr ⟨(mem_darts.mp hj).1, hm⟩)
  symm
  apply Surgery.countCycles_congr E
  intro x
  apply Subtype.ext
  rw [valE, facePerm_apply, valE]
  cases x with
  | inl d =>
    rw [Surgery.insertEdge_old _ ab]
    change _ = faceStep rows' d.val
    rw [old_step h huv hu hv hout fresh fresh']
    have ea : (facePerm h d = a) ↔ faceStep rows d.val = (u, k) := Subtype.ext_iff
    have eb : (facePerm h d = b) ↔ faceStep rows d.val = (v, j) := Subtype.ext_iff
    by_cases ha : facePerm h d = a
    · simp [ha, ea.mp ha, nameDart]
    by_cases hb : facePerm h d = b
    · simp [hb, ab.symm, eb.mp hb, huv.symm, nameDart]
    · simp [ha, hb, ea.not.mp ha, eb.not.mp hb, nameDart]
  | inr tag =>
    cases tag
    · rw [Surgery.insertEdge_first _ ab]
      change (v, j) = (v, (row rows' v).formPerm u)
      simp [hv, List.formPerm_apply_of_notMem fresh']
    · rw [Surgery.insertEdge_second]
      change (u, k) = (u, (row rows' u).formPerm v)
      simp [hu, List.formPerm_apply_of_notMem fresh]

/-- The old darts following the two insertion slots determine which faces change.
Their shared orbit splits, and distinct orbits merge. -/
theorem faceCount_insertEdge_corners {e : Edge} (G : SimpleInput n (pre ++ [e]))
    (con : ConnectedInput n pre) (legal : Legal n pre rows)
    (ins : rows' ∈ Rotations.insertEdge rows e) :
    ∃ a b : Dart rows, a.val.1 = e.1 ∧ b.val.1 = e.2 ∧
      (row rows' e.1).formPerm e.2 = a.val.2 ∧ (row rows' e.2).formPerm e.1 = b.val.2 ∧
      ((facePerm (valid_of_legal (simple_prefix G) legal)).SameCycle a b →
        faceCount rows' = faceCount rows + 1) ∧
      (¬ (facePerm (valid_of_legal (simple_prefix G) legal)).SameCycle a b →
        faceCount rows' + 1 = faceCount rows) := by
  obtain ⟨u, v⟩ := e
  have H := simple_prefix G
  have h := valid_of_legal H legal
  have legal' := legal_insertEdge legal ins
  have h' := valid_of_legal G legal'
  have edge : (u, v) ∈ pre ++ [(u, v)] := by simp
  have uv : u < v := G.ordered _ edge
  have vn : v < n := G.bounded _ edge
  have un := lt_trans uv vn
  have ur : u < rows.length := legal.1 ▸ un
  have vr : v < rows.length := legal.1 ▸ vn
  have missing : (u, v) ∉ pre := fun hm => (List.nodup_append.mp G.nodup).2.2 _ hm _ (by simp) rfl
  have missing' : (v, u) ∉ pre := fun hm => (Nat.lt_asymm uv (H.ordered _ hm))
  have fu : (u, v) ∉ darts rows := fun hm =>
    ((dart_iff H legal _).mp hm).elim missing missing'
  have fv : (v, u) ∉ darts rows := fun hm =>
    ((dart_iff H legal _).mp hm).elim missing' missing
  have members (x : Edge) : x ∈ darts rows' ↔ x ∈ darts rows ∨ x = (u, v) ∨ x = (v, u) := by
    rw [dart_iff G legal', dart_iff H legal]
    have eq : x.swap = (u, v) ↔ x = (v, u) := ⟨fun h => congrArg Prod.swap h,
      fun h => congrArg Prod.swap h⟩
    simp only [List.mem_append, List.mem_singleton, eq]
    tauto
  have nonempty (w : Nat) (hw : w < n) : row rows w ≠ [] := by
    obtain ⟨x, hx⟩ := SimpleInput.exists_neighbor con (by omega) w hw
    exact List.ne_nil_of_mem ((legal.2 w hw).mem_iff.mpr hx)
  obtain ⟨su, sv, rest⟩ := insertEdge_rows uv.ne ur vr ins
  have fresh : v ∉ row rows u := fun hm => fu (mem_darts.mpr ⟨ur, hm⟩)
  have fresh' : u ∉ row rows v := fun hm => fv (mem_darts.mpr ⟨vr, hm⟩)
  obtain ⟨k, hk, hku⟩ := slots_formPerm (nonempty u un) (h.nodup u) fresh su
  obtain ⟨j, hj, hjv⟩ := slots_formPerm (nonempty v vn) (h.nodup v) fresh' sv
  change (row rows' u).formPerm = swap v k * (row rows u).formPerm at hku
  change (row rows' v).formPerm = swap u j * (row rows v).formPerm at hjv
  let a : Dart rows := ⟨(u, k), mem_darts.mpr ⟨ur, hk⟩⟩
  let b : Dart rows := ⟨(v, j), mem_darts.mpr ⟨vr, hj⟩⟩
  have ab : a ≠ b := fun eq => uv.ne (congrArg (fun d : Dart rows => d.val.1) eq)
  have cnt := face_counts h h' uv.ne fu fv members a.prop b.prop hku hjv rest
  have normal (rs : Rows) (len : rs.length = n) (valid : Valid rs) :
      faceCount rs = Surgery.countCycles (facePerm valid) := by
    have ne : rs ≠ [[]] := by rintro rfl; simp at len; omega
    simp [faceCount_eq valid, ne, Surgery.countCycles]
  refine ⟨a, b, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change (row rows' u).formPerm v = k
    simp [hku, List.formPerm_apply_of_notMem fresh]
  · change (row rows' v).formPerm u = j
    simp [hjv, List.formPerm_apply_of_notMem fresh']
  · intro same
    rw [normal _ legal'.1 h', normal _ legal.1 h, cnt]
    exact Surgery.insertEdge_sameFace _ ab same
  · intro diff
    rw [normal _ legal'.1 h', normal _ legal.1 h, cnt]
    exact Surgery.insertEdge_differentFaces _ ab diff

/-- Adding a non-tree edge to a connected spanning rotation splits one face or merges two. -/
theorem faceCount_insertEdge {e : Edge} (G : SimpleInput n (pre ++ [e]))
    (con : ConnectedInput n pre) (legal : Legal n pre rows)
    (ins : rows' ∈ Rotations.insertEdge rows e) :
    faceCount rows' = faceCount rows + 1 ∨ faceCount rows' + 1 = faceCount rows := by
  obtain ⟨a, b, _, _, _, _, hs, hd⟩ := faceCount_insertEdge_corners G con legal ins
  exact (Classical.em _).imp hs hd

end MultiGenus.Extension
