import KneserConstruction.FamilyZeroRows

/-! # The complete zero-coordinate part of Construction 5.6 -/

noncomputable section

namespace BipartiteKneser.Family.Zero

open Fin.CommRing
open Coordinates

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime]

/-- First exponent in the usual orientation of index i. -/
def start (i : ℕ) : Fin q := ((2*i+1 : ℕ) : Fin q)

/-- Number of initial rows replaced by parity templates. -/
def cut (odd : Bool) := if odd then 3 else 2

/-- First exponents along the remaining path after its initial vertex.
The distinguished index j is moved to the end and oriented by v. -/
def tail (M j : ℕ) (odd : Bool) (v : Fin q) : List (Fin q) :=
  (((List.range' (cut odd + 1) (M - (cut odd + 1))).erase j).map start) ++ [v]

/-- Linear sequence of zero-coordinate successor rows. -/
def path (m : Multipliers p q) (k : Fin q) : List (Fin q) → List (Quad (Frame p q))
  | [] => []
  | l :: ls => step m k l :: path m l ls

/-- The parity rows, remaining zero path and two mixed attachment rows. -/
def rows (m : Multipliers p q) (M j : ℕ) (a b v : Fin q) : List (Quad (Frame p q)) :=
  let odd := decide (M % 2 = 1)
  templates m odd ++ path m (start (cut odd)) (tail M j odd v) ++ bridges m a b v

theorem path_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (k : Fin q)
    (ls : List (Fin q)) : ∀ Q ∈ path m k ls, Closed m Q := by
  induction ls generalizing k with
  | nil => simp [path]
  | cons l ls ih =>
    intro Q h
    rcases List.mem_cons.mp h with rfl | h
    · exact step_closed m h2 k l
    · exact ih l Q h

theorem rows_closed (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0)
    (M j : ℕ) (a b v : Fin q) (hv : v = 1 + a - b) (hs : mult m a + mult m b = -2) :
    ∀ Q ∈ rows m M j a b v, Closed m Q := by
  intro Q hQ
  simp only [rows, List.mem_append] at hQ
  rcases hQ with (h | h) | h
  · exact templates_closed m h2 _ Q h
  · exact path_closed m h2 _ _ Q h
  · exact bridges_closed m h2 a b hs v hv Q h

private theorem path_inventory (m : Multipliers p q) (k : Fin q) (ls : List (Fin q)) :
    ((path m k ls).map (Quad.domBag (inverse m))).sum + block m (ls.getLastD k) =
      ((k :: ls).map (block m)).sum ∧
    ((path m k ls).map (Quad.ranBag (inverse m))).sum + block m k =
      ((k :: ls).map (block m)).sum := by
  induction ls generalizing k with
  | nil => simp [path]
  | cons l ls ih =>
    have ⟨hd, hr⟩ := ih l
    have d : (step m k l).domBag (inverse m) = block m k := rfl
    have r : (step m k l).ranBag (inverse m) = block m l := add_comm ..
    simp only [path, List.map_cons, List.sum_cons, List.getLastD_cons, d, r] at *
    constructor
    · rw [add_assoc, hd]
    · calc
        _ = block m k + (((path m l ls).map (Quad.ranBag (inverse m))).sum + block m l) := by
          ac_rfl
        _ = _ := congrArg (block m k + ·) hr

private theorem moved {M j L : ℕ} (hj : L < j) (hM : j < M) :
    let s := List.range' (L+1) (M-(L+1))
    ((List.range L ++ [L]) ++ (s.erase j ++ [j])).Perm (List.range M) := by
  let s := List.range' (L+1) (M-(L+1))
  have hm : j ∈ s := by simp [s, List.mem_range'_1]; omega
  have he := (List.perm_append_singleton j (s.erase j)).trans (List.perm_cons_erase hm).symm
  have ht : List.range (L+1) ++ s = List.range M := by
    simp only [List.range_eq_range', s]
    convert List.range'_append_1 (s := 0) (m := L+1) (n := M-(L+1)) using 1 <;>
      simp [show L + 1 + (M - (L + 1)) = M by omega]
  rw [← ht, List.range_succ (n := L)]
  exact List.Perm.append_left _ he

private theorem initial_eq (m : Multipliers p q) (odd : Bool) :
    initial m odd = ((List.range (cut odd)).map (fun i => block m (start i))).sum := by
  cases odd <;> simp only [cut, ite_true, Bool.false_eq_true, ite_false, initial]
  all_goals norm_num [List.range_succ, start, add_assoc]

private theorem follow_eq (m : Multipliers p q) (odd : Bool) :
    following m odd + block m 1 = initial m odd + block m (start (cut odd)) := by
  cases odd <;> simp only [cut, initial, following, Bool.false_eq_true, ite_false, ite_true,
    add_zero]
  all_goals norm_num [start]; ac_rfl

/-- The natural index inventory, independent of the choice of orientation at j. -/
theorem blocks (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (M j : ℕ)
    (hj : 4 ≤ j) (hjM : j < M) (odd : Bool) (v : Fin q)
    (hv : v = start j ∨ v = -(start j + 1)) :
    initial m odd + ((start (cut odd) :: tail M j odd v).map (block m)).sum =
      ∑ i : Fin M, block m (start i.val) := by
  let L := cut odd
  have hL : L < j := by cases odd <;> dsimp [L, cut] <;> omega
  have hblock : block m v = block m (start j) := by
    rcases hv with rfl | rfl
    · rfl
    · exact block_reverse m h2 _
  have perm := moved hL hjM
  have he := (perm.map (fun i => block m (start i))).sum_eq
  rw [initial_eq]
  change _ + ((start L :: tail M j odd v).map (block m)).sum = _
  simp only [tail, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, List.map_map, Function.comp_def, hblock] at he ⊢
  rw [Fin.sum_univ_eq_sum_range (fun i => block m (start i)) M]
  have endEq := List.sum_toFinset (fun i => block m (start i)) (List.nodup_range (n := M))
  rw [List.toFinset_range] at endEq
  rw [endEq]
  simpa only [L, add_assoc] using he

/-- Domain and range counts of all zero rows, including both attachment rows. -/
theorem inventories (m : Multipliers p q) (h2 : (2 : ZMod p) ≠ 0) (M j : ℕ)
    (hj : 4 ≤ j) (hjM : j < M) (a b v : Fin q) (hv : v = start j ∨ v = -(start j + 1)) :
    let total := ∑ i : Fin M, block m (start i.val)
    ((rows m M j a b v).map (Quad.domBag (inverse m))).sum = total + quartet m a 1 ∧
    ((rows m M j a b v).map (Quad.ranBag (inverse m))).sum = total + quartet m b 1 := by
  let odd := decide (M % 2 = 1)
  let k : Fin q := start (cut odd)
  let ls := tail M j odd v
  obtain ⟨pd, pr⟩ := path_inventory m k ls
  have last : ls.getLastD k = v := by simp [ls, tail]
  rw [last] at pd
  have ⟨td,tr⟩ := templates_inventories m h2 odd
  have total := blocks m h2 M j hj hjM odd v hv
  let rr := templates m odd ++ path m k ls ++ bridges m a b v
  change (rr.map _).sum = _ ∧ (rr.map _).sum = _
  dsimp only [rr]
  simp only [List.map_append, List.sum_append, td, tr, bridges_domains m h2,
    bridges_ranges m h2]
  rw [← total]
  constructor
  · calc
      _ = initial m odd +
          (((path m k ls).map (Quad.domBag (inverse m))).sum + block m v) + quartet m a 1 := by
            ac_rfl
      _ = _ := by rw [pd]
  · calc
      _ = (following m odd + block m 1) +
          ((path m k ls).map (Quad.ranBag (inverse m))).sum + quartet m b 1 := by ac_rfl
      _ = _ := by
        rw [follow_eq]
        change _ + block m k + _ + _ = _
        rw [add_assoc (initial m odd), add_comm (block m k), pr]

end BipartiteKneser.Family.Zero
