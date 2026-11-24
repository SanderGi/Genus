/-
Copyright (c) 2026 Genus contributors. All rights reserved.
SPDX-License-Identifier: GPL-2.0-only
Authors: Genus contributors
-/
module

public import Page.ExactCover
public import Page.FaceBounds
public import Page.Turns
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Count

/-! # Pruning partial face covers

A face fixes the successor of each incoming dart, including its wraparound turn.
A prefix can extend to a rotation only if its darts are distinct and every local
cycle already closed has the full degree of its vertex.
-/

@[expose] public section

namespace Page.CheckedDFS

open MultiGenus MultiGenus.Rotations Walks ExactCover

/-- Consecutive darts of the selected faces, including the last-to-first turns. -/
def turns (chosen : Cover) : List (Dart × Dart) :=
  chosen.flatMap fun f => f.zip (f.rotate 1)

/-- Follow assigned turns for at most `fuel` steps, detecting a positive return to `start`. -/
def returns (next : Nat → Option Nat) (start current : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 => match next current with
    | none => false
    | some b => b == start || returns next start b fuel

private theorem path_of_returns {next : Nat → Option Nat} {a x fuel}
    (h : returns next a x fuel = true) :
    ∃ k, 0 < k ∧ k ≤ fuel ∧ Turns.Path (fun u v => next u = some v) k x a := by
  induction fuel generalizing x with
  | zero => simp [returns] at h
  | succ fuel ih =>
    cases e : next x with
    | none => simp [returns, e] at h
    | some y =>
      simp only [returns, e, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact ⟨1, by omega, by omega, (Turns.Path.nil x).snoc e⟩
      · obtain ⟨k, hk, bound, path⟩ := ih h
        exact ⟨k + 1, by omega, by omega, path.cons e⟩

/-- A prefix uses distinct incidences, has matching turn endpoints and contains no
proper cyclic component at any vertex. Each outgoing dart occurs exactly once whenever
the incoming darts are distinct, since each face pairs its word with a cyclic shift. -/
def compatible (degree : Nat → Nat) (chosen : Cover) : Bool :=
  let ts := turns chosen
  decide chosen.flatten.Nodup && ts.all fun (d, e) =>
    d.2 == e.1 && !returns (fun a => (ts.lookup (a, d.2)).map Prod.snd)
      d.1 d.1 (degree d.2 - 1)

private theorem of_lookup {ts : List (Dart × Dart)} {d e} (h : ts.lookup d = some e) :
    (d, e) ∈ ts := by
  induction ts with
  | nil => simp at h
  | cons p ts ih =>
    obtain ⟨x, y⟩ := p
    by_cases eq : d = x
    · subst x
      simp_all
    · exact List.mem_cons_of_mem _ (ih (by simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr eq]
        using h))

private theorem dart_of_turn {chosen : Cover} {d e : Dart} (nd : chosen.flatten.Nodup)
    (h : (d, e) ∈ turns chosen) : ∃ f ∈ chosen, d ∈ f ∧ f.formPerm d = e := by
  obtain ⟨f, hf, ht⟩ := List.mem_flatMap.mp h
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem ht
  simp only [List.getElem_zip] at eq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
  have nd' := (List.nodup_append.mp ((List.perm_cons_erase hf).flatten.nodup_iff.mp nd)).1
  exact ⟨f, hf, List.getElem_mem _, by rw [List.formPerm_apply_getElem _ nd', List.getElem_rotate]⟩

/-- Every selection of faces from a checked certificate passes the partial rotation test.
Subpermutation permits arbitrary order and preserves multiplicities. -/
theorem compatible_of_check {n es chosen fs} (G : SimpleInput n es)
    (ok : Certificate.check n es fs = true) (sub : chosen.Subperm fs) :
    compatible (fun v => (neighbors es v).length) chosen = true := by
  obtain ⟨whole, perm, incl⟩ := List.subperm_iff.mp sub
  have full := (Certificate.check_flatten_perm ok).nodup_iff.mpr (Certificate.universe_nodup G)
  have nd := (perm.flatten.nodup_iff.mpr full).sublist incl.flatten
  have subset : chosen ⊆ fs := fun _ h => perm.mem_iff.mp (incl.subset h)
  have m := Certificate.matches_readRows ok
  have turn {d e} (he : (d, e) ∈ turns chosen) :
      d ∈ Certificate.universe es ∧ e.1 = d.2 ∧ Turns.Recorded chosen d.2 d.1 e.2 := by
    obtain ⟨f, hf, hd, step⟩ := dart_of_turn nd he
    have endpoints := congrArg Prod.fst ((m _ (subset hf) _ hd).symm.trans step)
    exact ⟨(Certificate.check_flatten_perm ok).mem_iff.mp (List.mem_flatten.mpr
      ⟨f, subset hf, hd⟩), endpoints.symm, f, hf, hd, step.trans (Prod.ext endpoints.symm rfl)⟩
  simp only [compatible, decide_eq_true nd, Bool.true_and, List.all_eq_true]
  rintro ⟨d, e⟩ he
  obtain ⟨mem, fits, _⟩ := turn he
  simp only [fits, beq_self_eq_true, Bool.true_and, Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨k, pos, bound, path⟩ := path_of_returns bad
  have adj := (Certificate.mem_universe.mp mem).symm
  have hv := G.neighbor_lt (mem_neighbors.mpr adj.symm)
  have rowPerm := (Certificate.readRows_of_check G ok).1.2 d.2 hv
  have ha := rowPerm.mem_iff.mpr (mem_neighbors.mpr adj)
  have dvd := Turns.length_dvd_of_closed (rowPerm.nodup_iff.mpr (G.neighbors_nodup d.2)) ha
    (turn := fun a b => ((turns chosen).lookup (a, d.2)).map Prod.snd = some b) (by
      intro a b h
      obtain ⟨out, lookup, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Turns.extends_recorded m subset (turn (of_lookup lookup)).2.2) path
  have := rowPerm.length_eq ▸ Nat.le_of_dvd pos dvd
  omega

/-- Search for exactly `left` more faces, keeping the uncovered darts in input order. -/
def dfs (find : Finder) (check pass : Cover → Bool) (lo hi : Nat) :
    (left : Nat) → List (Nat × Nat) → Cover → Option Cover
  | 0, [], chosen => if check chosen then some chosen else none
  | 0, _ :: _, _ => none
  | _ + 1, [], _ => none
  | k + 1, d :: ds, chosen =>
    find d fun f =>
      let size := f.length
      let free := ds.length + 1 - size
      if lo ≤ size ∧ size ≤ hi ∧ k * lo ≤ free ∧ free ≤ k * hi then
        if f.all (· ∈ d :: ds) && pass (f :: chosen) then
          dfs find check pass lo hi k ((d :: ds).diff f) (f :: chosen)
        else none
      else none

/-- A successful search extends the face count of the prefix and passes the leaf checker. -/
theorem dfs_sound (pool : (Nat × Nat) → Cover) (check pass : Cover → Bool) (lo hi k : Nat)
    (remaining : List (Nat × Nat)) (chosen result : Cover)
    (h : dfs (fromLists pool) check pass lo hi k remaining chosen = some result) :
    check result = true ∧ result.length = k + chosen.length := by
  induction k generalizing remaining chosen with
  | zero =>
    cases remaining with
    | nil =>
      simp only [dfs] at h
      split at h <;> simp_all
    | cons => simp [dfs] at h
  | succ k ih =>
    cases remaining with
    | nil => simp [dfs] at h
    | cons d ds =>
      obtain ⟨f, _, hf⟩ := List.exists_of_findSome?_eq_some h
      dsimp only at hf
      split at hf
      · split at hf
        · obtain ⟨hc, hl⟩ := ih _ _ hf
          exact ⟨hc, by simp only [List.length_cons] at hl; omega⟩
        · contradiction
      · contradiction

private theorem leftover {r f g : List (Nat × Nat)} {fs : Cover}
    (cov : r.Perm (f ++ fs.flatten)) (rot : f.IsRotated g) : fs.flatten.Perm (r.diff g) := by
  apply List.perm_iff_count.mpr
  intro d
  rw [List.count_diff, cov.count_eq, List.count_append, ← rot.perm.count_eq]
  omega

/-- The unassigned faces reserve between these two dart budgets. -/
theorem flatten_bounds {lo hi : Nat} {fs : Cover}
    (bounds : ∀ f ∈ fs, lo ≤ f.length ∧ f.length ≤ hi) :
    fs.length * lo ≤ fs.flatten.length ∧ fs.flatten.length ≤ fs.length * hi := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    obtain ⟨lower, upper⟩ := bounds f (.head _)
    obtain ⟨l, u⟩ := ih fun g hg => bounds g (.tail _ hg)
    simp only [List.length_cons, Nat.succ_mul, List.flatten_cons, List.length_append]
    omega

/-- An accepted completion is found if every pending face can be rerooted at any of its darts. -/
theorem dfs_complete (pool : (Nat × Nat) → Cover) (check pass : Cover → Bool)
    (lo hi : Nat) (safe : ∀ {rest pre}, check (rest ++ pre) = true → pass pre = true)
    (bounds : ∀ {fs}, check fs = true → ∀ f ∈ fs, lo ≤ f.length ∧ f.length ≤ hi)
    (stable : Invariant check) (k : Nat) (remaining : List (Nat × Nat)) (chosen pending : Cover)
    (len : pending.length = k) (cov : pending.flatten.Perm remaining)
    (ok : check (pending ++ chosen) = true)
    (nonempty : ∀ f ∈ pending, f ≠ [])
    (rooted : ∀ f ∈ pending, ∀ d ∈ f, ∃ g ∈ pool d, f.IsRotated g) :
    (dfs (fromLists pool) check pass lo hi k remaining chosen).isSome := by
  induction k generalizing remaining chosen pending with
  | zero =>
    have hp : pending = [] := List.length_eq_zero_iff.mp len
    subst pending
    have hr : remaining = [] := cov.symm.eq_nil
    subst remaining
    simpa [dfs] using ok
  | succ k ih =>
    cases remaining with
    | nil =>
      obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < pending.length)
      have emp := cov.eq_nil
      simp only [List.flatten_cons, List.append_eq_nil_iff] at emp
      exact (nonempty _ (.head _) emp.1).elim
    | cons d ds =>
      obtain ⟨f, hf, hd⟩ := List.mem_flatten.mp (cov.mem_iff.mpr (.head _))
      obtain ⟨g, hg, rot⟩ := rooted f hf d hd
      let rest := pending.erase f
      have pick : pending.Perm (f :: rest) := List.perm_cons_erase hf
      have parts : (d :: ds).Perm (f ++ rest.flatten) := cov.symm.trans pick.flatten
      have fits : ∀ x ∈ g, x ∈ d :: ds := fun x hx =>
        parts.mem_iff.mpr (List.mem_append_left _ (rot.perm.mem_iff.mpr hx))
      change ((pool d).findSome? _).isSome
      apply List.findSome?_isSome_iff.mpr
      refine ⟨g, hg, ?_⟩
      have allowed : g.all (fun x => decide (x ∈ d :: ds)) = true :=
        List.all_eq_true.mpr fun x hx => decide_eq_true (fits x hx)
      have h₁ := stable.perm (pick.append_right chosen) ok
      have h₂ := stable.rotate rot (show check (f :: (rest ++ chosen)) = true from h₁)
      have ok' : check (rest ++ g :: chosen) = true := stable.perm List.perm_middle.symm h₂
      have glen := bounds h₂ g (.head _)
      have restLen : rest.length = k := by simp [rest, hf, len]
      have budget := flatten_bounds (fun w hw => bounds ok' w (List.mem_append_left _ hw))
      rw [restLen] at budget
      have total := parts.length_eq
      simp only [List.length_cons, List.length_append, rot.perm.length_eq] at total
      have slots : lo ≤ g.length ∧ g.length ≤ hi ∧
          k * lo ≤ ds.length + 1 - g.length ∧ ds.length + 1 - g.length ≤ k * hi := by omega
      simp only [slots, ite_true, allowed, safe ok', Bool.and_self]
      apply ih _ _ rest restLen (leftover parts rot) ok'
      · exact fun f hf => nonempty f (List.mem_of_mem_erase hf)
      · exact fun f hf => rooted f (List.mem_of_mem_erase hf)

end Page.CheckedDFS
