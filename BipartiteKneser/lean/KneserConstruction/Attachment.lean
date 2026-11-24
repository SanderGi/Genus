module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Selecting the square multipliers for the zero-coordinate attachment

For Lemma 5.5 we parametrize the equation A+B=−2 by
U=(t²−1)², V=(2t)², W=(t²+1)². Then U+V=W. A forbidden value of either
A=−2U/W or B=−2V/W eliminates at most eight parameters; so does a
forbidden ratio in either orientation.
-/

public section

namespace BipartiteKneser.Attachment

open Polynomial

variable {F : Type*} [Field F]

private noncomputable def u : F[X] := (X ^ 2 - 1) ^ 2
private noncomputable def v : F[X] := (2 * X) ^ 2
private noncomputable def w : F[X] := (X ^ 2 + 1) ^ 2

private noncomputable def badValue (c : F) : F[X] :=
  (-2 * u - C c * w) * (-2 * v - C c * w)

private noncomputable def badRatio (c : F) : F[X] :=
  (u - C c * v) * (v - C c * u)

private noncomputable def degenerate : F[X] := X * (X ^ 2 - 1) * (X ^ 2 + 1)

private theorem root_bound [DecidableEq F] (P : F[X]) {n : ℕ}
    (degree : P.natDegree ≤ n) : P.roots.toFinset.card ≤ n :=
  P.roots.toFinset_card_le.trans ((Polynomial.card_roots' P).trans degree)

private theorem outside_roots [DecidableEq F] (P : F[X]) (hp : P ≠ 0) {t : F}
    (ht : t ∉ P.roots.toFinset) : P.eval t ≠ 0 := by
  simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot] using ht

private theorem value_ne_zero [NeZero (2 : F)] {c : F} (hc : c ≠ 0) : badValue c ≠ 0 := by
  apply mul_ne_zero
  · intro eq
    have he := congrArg (Polynomial.eval (1 : F)) eq
    simp only [u, w, eval_sub, eval_mul, eval_neg, eval_C, eval_pow, eval_X,
      eval_one, one_pow, sub_self, eval_add,
      ← one_add_one_eq_two] at he
    have h₂ : (1 : F) + 1 ≠ 0 := by
      simpa only [one_add_one_eq_two] using (two_ne_zero : (2 : F) ≠ 0)
    simp [h₂, hc] at he
  · intro eq
    have he := congrArg (Polynomial.eval (0 : F)) eq
    simp [v, w, hc] at he

private theorem ratio_ne_zero {c : F} (hc : c ≠ 0) : badRatio c ≠ 0 := by
  apply mul_ne_zero <;> intro eq <;>
    have he := congrArg (Polynomial.eval (0 : F)) eq <;> simp [u, v, hc] at he

private theorem badValue_card [DecidableEq F] (c : F) :
    (badValue c).roots.toFinset.card ≤ 8 := by
  apply root_bound
  unfold badValue u v w
  compute_degree

private theorem badRatio_card [DecidableEq F] (c : F) :
    (badRatio c).roots.toFinset.card ≤ 8 := by
  apply root_bound
  unfold badRatio u v
  compute_degree

private theorem degenerate_card [DecidableEq F] :
    (degenerate (F := F)).roots.toFinset.card ≤ 5 := by
  apply root_bound
  unfold degenerate
  compute_degree

/-- Over any finite field with at least 131 elements in which −2 is a nonzero square,
one can avoid seven prescribed nonzero values for A and B and eight prescribed
nonzero values for both A/B and B/A simultaneously. -/
theorem exists_square_pair [Fintype F] [NeZero (2 : F)]
    (size : 131 ≤ Fintype.card F) (sq : IsSquare (-2 : F)) (values ratios : Finset F)
    (nv : values.card ≤ 7) (nr : ratios.card ≤ 8) (v0 : 0 ∉ values) (r0 : 0 ∉ ratios) :
    ∃ A B : F, A + B = -2 ∧ A ≠ 0 ∧ B ≠ 0 ∧ IsSquare A ∧ IsSquare B ∧
      A ∉ values ∧ B ∉ values ∧ A / B ∉ ratios ∧ B / A ∉ ratios := by
  classical
  let valRoots := values.biUnion fun c => (badValue c).roots.toFinset
  let ratRoots := ratios.biUnion fun c => (badRatio c).roots.toFinset
  let bad := (degenerate (F := F)).roots.toFinset ∪ valRoots ∪ ratRoots
  have hv : valRoots.card ≤ values.card * 8 :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun c _ => badValue_card c)
  have hr : ratRoots.card ≤ ratios.card * 8 :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun c _ => badRatio_card c)
  have tooFew : bad.card < (Finset.univ : Finset F).card := by
    have h₁ := Finset.card_union_le (degenerate (F := F)).roots.toFinset valRoots
    have h₂ := Finset.card_union_le ((degenerate (F := F)).roots.toFinset ∪ valRoots) ratRoots
    have h₃ := degenerate_card (F := F)
    unfold bad
    rw [Finset.card_univ]
    omega
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card tooFew
  have regular : (degenerate (F := F)).eval t ≠ 0 := by
    apply outside_roots
    · unfold degenerate
      exact mul_ne_zero (mul_ne_zero X_ne_zero (X_pow_sub_C_ne_zero (by decide) 1))
        (by simpa using (X_pow_sub_C_ne_zero (R := F) (n := 2) (by decide) (-1)))
    · exact fun h => ht (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have h0 : t ≠ 0 ∧ t ^ 2 - 1 ≠ 0 ∧ t ^ 2 + 1 ≠ 0 := by
    simpa [degenerate, mul_assoc] using regular
  let U := (t ^ 2 - 1) ^ 2
  let V := (2 * t) ^ 2
  let W := (t ^ 2 + 1) ^ 2
  have hU : U ≠ 0 := pow_ne_zero _ h0.2.1
  have hV : V ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero h0.1)
  have hW : W ≠ 0 := pow_ne_zero _ h0.2.2
  have total : U + V = W := by dsimp [U, V, W]; ring
  let A := -2 * U / W
  let B := -2 * V / W
  have hA : A ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hU) hW
  have hB : B ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hV) hW
  have sqPow (x : F) : IsSquare (x ^ 2) := ⟨x, pow_two x⟩
  have noValue (c : F) (hc : c ∈ values) : A ≠ c ∧ B ≠ c := by
    have ne : (badValue c).eval t ≠ 0 := outside_roots _ (value_ne_zero (fun e => v0 (e ▸ hc)))
      (fun hm => ht (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨c, hc, hm⟩))))
    have prod : (-2 * U - c * W) * (-2 * V - c * W) ≠ 0 := by
      simpa [badValue, U, V, W, u, v, w] using ne
    constructor <;> intro eq <;> apply prod
    · rw [sub_eq_zero.mpr ((div_eq_iff hW).mp eq), zero_mul]
    · rw [sub_eq_zero.mpr ((div_eq_iff hW).mp eq), mul_zero]
  have noRatio (c : F) (hc : c ∈ ratios) : A / B ≠ c ∧ B / A ≠ c := by
    have ne : (badRatio c).eval t ≠ 0 := outside_roots _ (ratio_ne_zero (fun e => r0 (e ▸ hc)))
      (fun hm => ht (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hc, hm⟩)))
    have prod : (U - c * V) * (V - c * U) ≠ 0 := by simpa [badRatio, u, v, U, V] using ne
    have ab : A / B = U / V := by dsimp [A, B]; field_simp
    have ba : B / A = V / U := by dsimp [A, B]; field_simp
    constructor <;> intro eq <;> apply prod
    · rw [sub_eq_zero.mpr ((div_eq_iff hV).mp (ab.symm.trans eq)), zero_mul]
    · rw [sub_eq_zero.mpr ((div_eq_iff hU).mp (ba.symm.trans eq)), mul_zero]
  refine ⟨A, B, ?_, hA, hB, (sq.mul (sqPow _)).div (sqPow _),
    (sq.mul (sqPow _)).div (sqPow _), fun h => (noValue _ h).1 rfl,
    fun h => (noValue _ h).2 rfl, fun h => (noRatio _ h).1 rfl, fun h => (noRatio _ h).2 rfl⟩
  dsimp [A, B]
  rw [← add_div, ← mul_add, total, mul_div_cancel_right₀ _ hW]

end BipartiteKneser.Attachment
