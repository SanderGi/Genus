module

public import KneserConstruction.CoordinateSpecial
public import KneserConstruction.CoordinateResidues

/-!
# Missing exponent pairs and their quadratic character

The Cayley transform identifies an oriented missing coordinate with a unique
multiplier. Folding its two signs counts each missing exponent pair once.
-/

@[expose] public section

namespace BipartiteKneser.Coordinates

variable {p q r : ℕ} [Fact p.Prime] [NeZero p] [NeZero q] (m : Multipliers p q)

/-- The actual positive-character bit of the field at the natural coordinate. -/
noncomputable def missingBit (p : ℕ) [Fact p.Prime] (w : ℕ) : Bool :=
  decide (quadraticChar (ZMod p) (1 - 4 * (w : ZMod p) ^ 2) = 1)

theorem v_eq_iff_mult (h₂ : (2 : ZMod p) ≠ 0) (k : Fin q) (w : ZMod p)
    (hp : 1 + 2 * w ≠ 0) :
    v m k = w ↔ mult m k = (1 - 2 * w) / (1 + 2 * w) := by
  rw [v, div_eq_iff (mul_ne_zero h₂ (one_add_mult_ne_zero m k)), eq_div_iff hp]
  constructor <;> intro he <;> linear_combination -he

/-- Outside the totally excluded fiber, the quadratic character detects the
unique oriented missing exponent. The exponent is nonzero when w is nonzero. -/
theorem character_iff_missing (res : p % 8 = 3) (w : ZMod p)
    (hp : w ≠ 1 / 2) (hn : w ≠ -(1 / 2)) :
    quadraticChar (ZMod p) (1 - 4 * w ^ 2) = 1 ↔ ∃! k, v m k = w := by
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  have A : 1 - 2 * w ≠ 0 := by
    intro he
    apply hp
    apply (eq_div_iff h₂).2
    linear_combination -he
  have B : 1 + 2 * w ≠ 0 := by
    intro he
    apply hn
    field_simp [h₂]
    linear_combination he
  have fac : 1 - 4 * w ^ 2 = (1 - 2 * w) * (1 + 2 * w) := by ring
  rw [quadraticChar_one_iff_isSquare (by rw [fac]; exact mul_ne_zero A B), fac]
  have eq : (1 - 2 * w) * (1 + 2 * w) =
      ((1 - 2 * w) / (1 + 2 * w)) * ((1 + 2 * w) * (1 + 2 * w)) := by field_simp [B]
  have sq : IsSquare ((1 + 2 * w) * (1 + 2 * w)) := ⟨_, rfl⟩
  constructor
  · intro hs
    have hd := hs.div sq
    rw [eq, mul_div_cancel_right₀ _ (mul_ne_zero B B)] at hd
    obtain ⟨k, hk⟩ := m.exists_log (by omega) (div_ne_zero A B) hd
    have e := (v_eq_iff_mult m h₂ k w B).2 hk
    exact ⟨k, e, fun j hj => v_injective m h₂ (hj.trans e.symm)⟩
  · rintro ⟨k, hk, _⟩
    rw [eq, ← (v_eq_iff_mult m h₂ k w B).1 hk]
    exact (m.square k).mul sq

/-- Positive representative of a field coordinate up to sign. -/
def foldCoord (w : ZMod p) : ℕ := min w.val (-w).val

private theorem cast_fold (w : ZMod p) : (foldCoord w : ZMod p) = w ∨
    (foldCoord w : ZMod p) = -w := by
  unfold foldCoord
  rcases min_choice w.val (-w).val with h | h <;> simp [h]

omit [NeZero p] in
theorem fold_neg (w : ZMod p) : foldCoord (-w) = foldCoord w := by
  simp [foldCoord, min_comm]

omit [NeZero q] in
private theorem fold_pos_le (size : p = 2 * q + 1) {w : ZMod p} (hw : w ≠ 0) :
    0 < foldCoord w ∧ foldCoord w ≤ q := by
  let _ : NeZero w := ⟨hw⟩
  have hv := w.val_lt
  have hz : w.val ≠ 0 := by simpa using hw
  unfold foldCoord
  rw [ZMod.val_neg_of_ne_zero]
  omega

omit [NeZero q] in
theorem fold_nat (size : p = 2 * q + 1) {w : ℕ} (h₁ : 0 < w) (h₂ : w ≤ q) :
    foldCoord (w : ZMod p) = w := by
  have hlt : w < p := by omega
  let _ : NeZero (w : ZMod p) := ⟨natCast_ne_zero_of_lt h₁ hlt⟩
  simp only [foldCoord, ZMod.val_neg_of_ne_zero, ZMod.val_natCast_of_lt hlt]
  omega

/-- Equality of folded coordinates means equality up to a sign. -/
theorem fold_eq {x y : ZMod p} (h : foldCoord x = foldCoord y) : x = y ∨ x = -y := by
  have e := congrArg (Nat.cast : ℕ → ZMod p) h
  rcases cast_fold x with a | a <;> rcases cast_fold y with b | b <;> grind

theorem ordinary_ne_half (size : p = 2 * q + 1) (h₂ : (2 : ZMod p) ≠ 0)
    {w : ℕ} (h₁ : 0 < w) (h₂' : w < q) :
    (w : ZMod p) ≠ 1 / 2 ∧ (w : ZMod p) ≠ -(1 / 2) := by
  have f := fold_nat size h₁ h₂'.le
  have qpos : 0 < q := NeZero.pos _
  have g := fold_nat size qpos le_rfl
  rw [top_fiber h₂ size, fold_neg] at g
  constructor <;> intro he <;> rw [he] at f
  · omega
  · rw [fold_neg] at f
    omega

/-- At an ordinary fiber, membership amounts to avoiding the folded missing address. -/
theorem present_iff_fold (size : p = 2 * q + 1) (h₂ : (2 : ZMod p) ≠ 0)
    {w : ℕ} (h₁ : 0 < w) (h₂' : w < q) (k : Fin q) :
    separated m.power (X m k w) = true ↔ w ≠ foldCoord (v m k) := by
  obtain ⟨a, b⟩ := ordinary_ne_half size h₂ h₁ h₂'
  rw [separated_X_iff m h₂]
  have f := fold_nat size h₁ h₂'.le
  constructor
  · rintro ⟨_, _, c, d⟩ he
    exact (fold_eq (f.trans he)).elim c d
  · intro h
    refine ⟨a, b, ?_, ?_⟩ <;> intro he <;> rw [he] at f
    · exact h f.symm
    · rw [fold_neg] at f
      exact h f.symm

/-- The unsigned missing address of a positive exponent representative. -/
noncomputable def missingAddress (qsize : q = 2 * r + 1) (i : Fin r) :=
  foldCoord (v m ((signedResidueEquiv qsize (i, false)).val))

/-- The address map enumerates precisely the positive-character fibers. -/
theorem missingAddress_image (size : p = 2 * q + 1) (qsize : q = 2 * r + 1) (res : p % 8 = 3) :
    (Finset.univ.image (missingAddress m qsize) =
      (Finset.Icc 1 (q - 1)).filter (fun w => missingBit p w = true)) ∧
      Function.Injective (missingAddress m qsize) := by
  classical
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  let e := signedResidueEquiv qsize
  let k (i : Fin r) := (e (i, false)).val
  have kn (i : Fin r) : (e (i, true)).val = -k i := by
    simp [e, k]
  let addr (i : Fin r) := foldCoord (v m (k i))
  have addr_lt (i : Fin r) : 0 < addr i ∧ addr i < q := by
    have h := fold_pos_le size (v_ne_zero m h₂ (e (i, false)).property)
    suffices addr i ≠ q by change 0 < addr i ∧ addr i ≤ q at h; omega
    intro he
    have a := cast_fold (v m (k i))
    change (addr i : ZMod p) = _ ∨ (addr i : ZMod p) = _ at a
    rw [he, top_fiber h₂ size] at a
    have b := v_ne_half m h₂ (k i)
    have c := v_ne_neg_half m h₂ (k i)
    grind
  have char {w : ℕ} (h₁ : 0 < w) (h₂' : w < q) :
      missingBit p w = true ↔ ∃! j, v m j = (w : ZMod p) := by
    simpa [missingBit] using character_iff_missing m res w (ordinary_ne_half size h₂ h₁ h₂').1
      (ordinary_ne_half size h₂ h₁ h₂').2
  have image_eq : Finset.univ.image addr =
      (Finset.Icc 1 (q - 1)).filter (fun w => missingBit p w = true) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨ha, hb⟩ := addr_lt i
      refine ⟨⟨ha, by omega⟩, (char ha hb).2 ?_⟩
      obtain h | h := cast_fold (v m (k i))
      · exact ⟨k i, h.symm, fun j hj => v_injective m h₂ (hj.trans h)⟩
      · rw [← v_neg m h₂] at h
        exact ⟨-k i, h.symm, fun j hj => v_injective m h₂ (hj.trans h)⟩
    · rintro ⟨⟨ha, hb⟩, hc⟩
      have lt : w < q := by have := NeZero.pos q; omega
      obtain ⟨j, hj, _⟩ := (char ha lt).1 hc
      have j0 : j ≠ 0 := by
        intro hz
        rw [hz, v_zero] at hj
        exact natCast_ne_zero_of_lt ha (by omega) hj.symm
      obtain ⟨⟨i, s⟩, hs⟩ := e.surjective ⟨j, j0⟩
      have eq := congrArg Subtype.val hs
      have f := fold_nat size ha lt.le
      cases s
      · change k i = j at eq
        exact ⟨i, by simp only [addr, eq, hj, f]⟩
      · change (e (i, true)).val = j at eq
        rw [kn] at eq
        rw [← eq, v_neg m h₂] at hj
        exact ⟨i, by rw [← hj, fold_neg] at f; exact f⟩
  have inj : Function.Injective addr := by
    intro i j he
    rcases (same_missing_pair_iff m h₂ _ _).1 (fold_eq he) with h | h
    · exact congrArg Prod.fst (e.injective (Subtype.ext h))
    · rw [← kn] at h
      exact congrArg Prod.fst (e.injective (Subtype.ext h))
  exact ⟨image_eq, inj⟩

include m in
/-- Exactly one positive field fiber is lost for each positive exponent representative. -/
theorem missingBit_count (size : p = 2 * q + 1) (qsize : q = 2 * r + 1) (res : p % 8 = 3) :
    ((Finset.Icc 1 (q - 1)).filter (fun w => missingBit p w = true)).card = r := by
  obtain ⟨eq, inj⟩ := missingAddress_image m size qsize res
  rw [← eq, Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]

/-- The number of present positive exponent representatives, with the actual missing bit. -/
theorem present_count (size : p = 2 * q + 1) (qsize : q = 2 * r + 1) (res : p % 8 = 3)
    {w : ℕ} (pos : 0 < w) (lt : w < q) :
    (Finset.univ.filter (fun i : Fin r =>
      separated m.power (X m (Fin.ofNat q (i.val + 1)) (w : ZMod p)))).card +
      (missingBit p w).toNat = r := by
  classical
  have h₂ : (2 : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by decide) (by omega)
  obtain ⟨eq, inj⟩ := missingAddress_image m size qsize res
  let addr := missingAddress m qsize
  have pred (i : Fin r) : separated m.power (X m (Fin.ofNat q (i.val + 1)) (w : ZMod p)) = true ↔
      w ≠ addr i := by
    simpa [addr, missingAddress] using present_iff_fold m size h₂ pos lt (Fin.ofNat q (i.val + 1))
  simp only [pred]
  have bound : (Finset.univ.filter (fun i => w = addr i)).card ≤ 1 := by
    exact Finset.card_le_one.mpr fun _ hi _ hj =>
      inj ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  have exists_at : (∃ i, w = addr i) ↔ missingBit p w = true := by
    have he := Finset.ext_iff.mp eq w
    simpa [addr, eq_comm (a := w), pos, show 1 ≤ w by omega,
      show w ≤ q - 1 by omega] using he
  have parts := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun i => w ≠ addr i)
  simp only [not_not, Finset.card_univ, Fintype.card_fin] at parts
  cases hb : missingBit p w
  · have no : (Finset.univ.filter (fun i => w = addr i)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := exists_at.mp ⟨i, (Finset.mem_filter.mp hi).2⟩
      simp_all
    simp_all
  · have yes : 0 < (Finset.univ.filter (fun i => w = addr i)).card := by
      obtain ⟨i, hi⟩ := exists_at.mpr hb
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp only [Bool.toNat_true]
    omega

include m in
/-- The character count in the constructor's ordered word of positive fibers. -/
theorem missingBit_count_list (size : p = 2 * q + 1) (qsize : q = 2 * r + 1)
    (res : p % 8 = 3) :
    ((List.range' 1 (q - 1)).map (missingBit p)).count true = r := by
  have h := (List.nodup_range' (s := 1) (n := q - 1)).card_eq_countP
    (P := fun w => missingBit p w = true)
  rw [List.toFinset_range'_1_1, missingBit_count m size qsize res] at h
  simpa [List.count_eq_countP, List.countP_map, Function.comp_def] using h.symm

end BipartiteKneser.Coordinates
