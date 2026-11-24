module

public import Std

/-!
# Counting faces of a rotation system

A face partition lists the darts of each orbit in traversal order. The flattened
list contains every dart exactly once. This suffices both for the Euler lower
bound and for counting the faces of a quadrangulation.
-/

@[expose] public section

set_option linter.all true

namespace BipartiteKneser

/-- The facial map takes every dart to the next in a nonempty cyclic list. -/
def FacialCycle {α : Type} (f : α → α) (face : List α) : Prop :=
  ∃ a tail, face = a :: tail ∧ face.map f = tail ++ [a]

/-- Each dart occurs once in the listed facial cycles, up to reordering. -/
def FacePartition {α : Type} (f : α → α) (darts : List α) (faces : List (List α)) : Prop :=
  faces.flatten.Perm darts ∧ ∀ face ∈ faces, FacialCycle f face

/-- A facial map with no returns after one, two, or three steps. -/
def GirthFour {α : Type} (f : α → α) : Prop :=
  ∀ x, f x ≠ x ∧ f (f x) ≠ x ∧ f (f (f x)) ≠ x

private theorem cycle_length {α : Type} {f : α → α} (hg : GirthFour f)
    {l : List α} (hl : FacialCycle f l) : 4 ≤ l.length := by
  obtain ⟨a, tail, rfl, he⟩ := hl
  have := hg a
  match tail with
  | [] | [_] | [_, _] => simp_all
  | _ :: _ :: _ :: _ => simp

private theorem length_sum_ge {α : Type} (ls : List (List α))
    (h : ∀ l ∈ ls, 4 ≤ l.length) : 4 * ls.length ≤ ls.flatten.length := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have := ih (fun m hm => h m (by simp [hm]))
    have := h l (by simp)
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- Every face uses at least four darts. -/
theorem face_bound {α : Type} {f : α → α} {darts faces} (hg : GirthFour f)
    (p : FacePartition f darts faces) : 4 * faces.length ≤ darts.length := by
  rw [← p.1.length_eq]
  exact length_sum_ge faces (fun l hl => cycle_length hg (p.2 l hl))

/-- Partition a finite, invariant list into quadrilaterals. The proof removes
one actual orbit at a time and shows that its complement is still invariant. -/
theorem four_partition {α : Type} (f : α → α)
    (hg : GirthFour f) (closes : ∀ x, f (f (f (f x))) = x)
    (darts : List α) (nd : darts.Nodup) (closed : ∀ x ∈ darts, f x ∈ darts) :
    ∃ fs, FacePartition f darts fs ∧ 4 * fs.length = darts.length := by
  classical
  match darts with
  | [] => exact ⟨[], by simp [FacePartition], rfl⟩
  | x :: xs =>
    let orbit := [x, f x, f (f x), f (f (f x))]
    let rest := (x :: xs).filter (fun y => decide (y ∉ orbit))
    have short := hg x
    have short₁ := hg (f x)
    have short₂ := hg (f (f x))
    have unique : orbit.Nodup := by simp [orbit]; grind
    have in_list : ∀ y ∈ orbit, y ∈ x :: xs := by
      intro y hy
      have h₀ : x ∈ x :: xs := by simp
      have h₁ := closed _ h₀
      have h₂ := closed _ h₁
      have h₃ := closed _ h₂
      simp only [orbit, List.mem_cons, List.not_mem_nil, or_false] at hy
      grind
    have rest_nd : rest.Nodup := List.Pairwise.filter _ nd
    have both_nd : (orbit ++ rest).Nodup := by
      rw [List.nodup_append]
      exact ⟨unique, rest_nd, by simp [rest]; grind⟩
    have perm : (orbit ++ rest).Perm (x :: xs) := by
      apply (List.perm_ext_iff_of_nodup both_nd nd).mpr
      intro y
      simp [rest]
      grind
    have rest_closed : ∀ y ∈ rest, f y ∈ rest := by
      intro y hy
      simp only [rest, List.mem_filter, decide_eq_true_eq] at hy ⊢
      refine ⟨closed _ hy.1, ?_⟩
      have back := closes y
      simp only [orbit, List.mem_cons, List.not_mem_nil, or_false] at *
      grind
    have len := perm.length_eq
    simp [orbit] at len
    have smaller : rest.length < (x :: xs).length := by simp only [List.length_cons]; omega
    obtain ⟨fs, ⟨hfs, legal⟩, count⟩ := four_partition f hg closes rest rest_nd rest_closed
    refine ⟨orbit :: fs, ⟨?_, ?_⟩, ?_⟩
    · exact (hfs.append_left orbit).trans perm
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨x, [f x, f (f x), f (f (f x))], rfl, by simp [orbit, closes]⟩
      · exact legal l hl
    · simp
      omega
termination_by darts.length
decreasing_by exact smaller

end BipartiteKneser
