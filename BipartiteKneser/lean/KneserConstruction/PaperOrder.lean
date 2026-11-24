module

public import KneserConstruction.FiberOrder
public import KneserConstruction.FamilyFiberRows
public import KneserConstruction.CoordinateEndpoints
public import KneserConstruction.Parameters

/-! # The prescribed exponent order in each nonzero coordinate fiber -/

@[expose] public section

namespace BipartiteKneser.Family.FiberOrder

open Coordinates

variable {p q r : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- The two residue cases of Construction 4.11. -/
def paperCase (p : ℕ) : FiberJoins.Case := if p % 3 = 1 then .one else .two

omit [NeZero p] [NeZero q] [Fact p.Prime] in
private theorem missing_cast :
    FiberJoins.missing (paperCase p) q = (Coordinates.w₀ p q : ℤ) ∨ q < 2 := by
  by_cases h : 2 ≤ q
  · left
    unfold paperCase Coordinates.w₀
    split <;> simp [FiberJoins.missing, Nat.cast_sub h]
  · omega

/-- Actual oriented choices for one fiber, together with completeness of its
quartets and the number of exponent representatives traversed by the rotation. -/
theorem exists_middle (d : Special m) (P : Parameters.Exponents m d.K d.N d.E)
    (size : p = 2 * q + 1) (qsize : q = 2 * r + 1) (large : 131 ≤ p) (res : p % 8 = 3)
    (i : Fin (q - 1)) :
    let f := firstExp (paperCase p) d.N d.E i
    let l := lastExp d.K d.E i
    ∃ mid : List (Fin q),
      ((fiberOrder f l P.a P.b mid (decide (i.val = 0))).map (quartet m · (coord i))).sum =
        (∑ k : Fin r, if separated m.power (X m (Fin.ofNat q (k.val + 1)) (coord i)) then
          quartet m (Fin.ofNat q (k.val + 1)) (coord i) else 0) ∧
      (fiberOrder f l P.a P.b mid (decide (i.val = 0))).length +
        (missingBit p (i.val + 1)).toNat = r := by
  classical
  dsimp only
  have sm : 19 ≤ p := by omega
  obtain ⟨hk, hn, he, kn, kn', ke, ke', ne, ne'⟩ := d.distinct sm
  have h₂ := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega : 2 < p)
  let k : Exponent q := ⟨d.K, hk⟩
  let n : Exponent q := ⟨d.N, hn⟩
  let e : Exponent q := ⟨d.E, he⟩
  let a : Exponent q := ⟨P.a, (P.avoid 0 (by simp)).1⟩
  let b : Exponent q := ⟨P.b, (P.avoid 0 (by simp)).2⟩
  let w := i.val + 1
  let key' := key qsize
  have positive : 0 < w := by dsimp [w]; omega
  have upper : w < q := by have := i.isLt; dsimp [w]; omega
  have mis := (missing_cast (p := p) (q := q)).resolve_right (by omega)
  let f := if w = Coordinates.w₀ p q then e else n
  let l := if w = q - 1 then e else k
  have valf : f.val = firstExp (paperCase p) d.N d.E i := by
    have cond : (i.val : ℤ) + 1 = FiberJoins.missing (paperCase p) q ↔ w = Coordinates.w₀ p q := by
      rw [mis]
      dsimp [w]
      omega
    by_cases hit : w = Coordinates.w₀ p q <;> simp [firstExp, cond, f, hit, e, n]
  have vall : l.val = lastExp d.K d.E i := by
    by_cases hit : i.val + 1 = q - 1 <;> simp [l, w, lastExp, hit, e, k]
  have wk : Coordinates.w₀ p q ≠ q - 1 := by unfold Coordinates.w₀; split <;> omega
  have keys (x y : Exponent q) (h : x.val ≠ y.val) (h' : x.val ≠ -y.val) :
      key' x ≠ key' y := fun eq => ((key_eq_iff qsize x y).mp eq).elim h h'
  have kkn : key' k ≠ key' n := keys k n kn kn'
  have kke : key' k ≠ key' e := keys k e ke ke'
  have kne : key' n ≠ key' e := keys n e ne ne'
  have kab : key' a ≠ key' b := keys a b P.distinct.1 P.distinct.2
  have av (t : Exponent q) (ht : t.val ∈ [0,d.K,-d.K,d.N,-d.N,d.E,-d.E])
      (hneg : -t.val ∈ [0,d.K,-d.K,d.N,-d.N,d.E,-d.E]) :
      key' a ≠ key' t ∧ key' b ≠ key' t :=
    ⟨keys a t (P.avoid _ ht).1 (P.avoid _ hneg).1,
     keys b t (P.avoid _ ht).2 (P.avoid _ hneg).2⟩
  have ak := av k (by simp [k]) (by simp [k])
  have an := av n (by simp [n]) (by simp [n])
  have ae := av e (by simp [e]) (by simp [e])
  let front := if i.val = 0 then [f,a,b] else [f]
  have unique : ((front ++ [l]).map key').Nodup := by
    dsimp only [front,f,l]
    split_ifs <;> simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil] <;> grind
  have fld : coord i = (w : ZMod p) := rfl
  have goodF : separated m.power (X m f.val (coord i)) = true := by
    rw [fld]
    dsimp only [f]
    split_ifs with hw
    · rw [hw]; exact (d.present_E_endpoints size sm).2
    · exact (d.present_N_iff size sm positive upper).mpr hw
  have goodL : separated m.power (X m l.val (coord i)) = true := by
    rw [fld]
    dsimp only [l]
    split_ifs with hw
    · rw [hw]; exact (d.present_E_endpoints size sm).1
    · exact (d.present_K_iff size sm positive upper).mpr hw
  have allowed : ∀ x ∈ front ++ [l], key qsize x ∈ present qsize m (coord i) := by
    intro x hx
    have good : separated m.power (X m x.val (coord i)) = true := by
      simp only [front] at hx
      split_ifs at hx with hi
      · have eq : coord i = (1 : ZMod p) := by simp [coord,hi]
        have ga := d.present_at_one size sm res (P.avoid d.N (by simp)).1
          (P.avoid (-d.N) (by simp)).1
        have gb := d.present_at_one size sm res (P.avoid d.N (by simp)).2
          (P.avoid (-d.N) (by simp)).2
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact goodF
        · exact eq ▸ ga
        · exact eq ▸ gb
        · exact goodL
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · exact goodF
        · exact goodL
    simp only [present, List.mem_filter, List.mem_finRange, true_and]
    rcases signed qsize x with h | h
    · simpa only [h] using good
    · rw [h, (present_signs m h₂ _ _).1] at good
      exact good
  let mid := middle qsize m (coord i) front l
  refine ⟨mid.map Subtype.val, ?_, ?_⟩
  all_goals
    have actual : (order qsize m (coord i) front l).map Subtype.val =
        fiberOrder (firstExp (paperCase p) d.N d.E i) (lastExp d.K d.E i) P.a P.b
          (mid.map Subtype.val) (decide (i.val = 0)) := by
      unfold order fiberOrder
      rw [← valf, ← vall]
      by_cases hi : i.val = 0 <;> simp [hi, front, mid, a, b]
    rw [← actual]
  · rw [List.map_map]
    simpa only [val_pos, Function.comp_def] using
      inventory qsize m (coord i) h₂ front l unique allowed
  · have hl := (perm_keys qsize m (coord i) front l unique allowed).length_eq
    simp only [List.length_map] at hl ⊢
    rw [hl]
    have eq : (present qsize m (coord i)).toFinset = (Finset.univ.filter fun j : Fin r =>
        separated m.power (X m (Fin.ofNat q (j.val + 1)) (w : ZMod p))) := by
      ext j
      simp [present, val_pos, fld]
    have nd : (present qsize m (coord i)).Nodup := (List.nodup_finRange r).filter _
    rw [← List.toFinset_card_of_nodup nd, eq]
    exact present_count m size qsize res positive upper

end BipartiteKneser.Family.FiberOrder
