module

public import KneserConstruction.Family
public import KneserConstruction.OrbitJoin
public import KneserConstruction.OrbitLayout
public import KneserConstruction.OrbitZero

/-! # Every connection label drains to a retained first-frame port -/

@[expose] public section

noncomputable section

namespace BipartiteKneser.FamilyDrain

open Family Coordinates Orbit Reduction Boundary

variable {p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] {m : Multipliers p q}

/-- Every translation-row source belongs either to an indexed translation block or
to the exceptional E block at the last fiber. -/
private theorem translation_source (L : Translations.Layout r) (E : Fin q) (wa wb : ZMod p)
    (i : Translations.Row r) (s : Slot) :
    let Q := Translations.row m L E wa wb i
    (∃ t j, Q.dom (inverse m) s =
      pairBlock (m := m) (Translations.U t) (Translations.V (r := r) t) j) ∨
    (∃ j, Q.dom (inverse m) s = fiber m E wa j) := by
  dsimp only
  rw [← Translations.domain_val]
  rcases (Translations.domain L (i,s)) with ⟨_ | t,b,d⟩
  · right
    cases b <;> cases d
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · left
    refine ⟨t, rowSlot (b,d), ?_⟩
    cases b <;> cases d <;> rfl

/-- Domain slots of a K-to-N joining row belong to the final K block. -/
private theorem join_source (C : Construction m) (i : Fin (q - 2)) (s : Slot) :
    ∃ t : Fin (q - 1), ∃ j, (C.joins i).dom (inverse m) s = fiber m (C.last t) (coord t) j := by
  let t : Fin (q - 1) := ⟨i.val, by have := i.isLt; omega⟩
  have hn : t.val + 1 ≠ q - 1 := by have := i.isLt; dsimp [t]; omega
  have cw : ((Joins.number i : ℤ) : ZMod p) = coord t := by simp [Joins.number, coord,t]
  refine ⟨t, rowSlot s, ?_⟩
  rcases s with ⟨b,d⟩
  cases b <;> cases d <;>
    simp only [Construction.joins, Joins.row, Quad.dom, Construction.last, lastExp, hn, ite_false,
      cw] <;> rfl

/-- Drain every source slot of every actual row. The transition from a final block to
the next first block is the second local-path assertion of the orbit reduction. -/
theorem drain (C : Construction m) (switch : ℕ → Bool) (hc : C.CoversOrders)
    (lastFirst : ∀ (w j : ℕ), 1 ≤ w → w < q → j < 4 →
      Reach (onFrames (C.complete switch hc)) (lastFrame m C.special.K C.special.E (slotPoint w j))
        (firstFrame (boundaryCase p) m C.special.N C.special.E (routePoint (boundaryCase p) q w j)))
    (x : Family.Label m) :
    ∃ w : ℕ, 1 ≤ w ∧ w < q ∧ ∃ j : Fin 4, Reach (onFrames (C.complete switch hc)) x.val
      (firstFrame (boundaryCase p) m C.special.N C.special.E (slotPoint w j.val)) := by
  let F := C.complete switch hc
  let hits (y : Frame p q) := ∃ w : ℕ, 1 ≤ w ∧ w < q ∧ ∃ j : Fin 4,
    Reach (onFrames F) y (firstFrame (boundaryCase p) m C.special.N C.special.E (slotPoint w j.val))
  change hits x.val
  have pull {y z : Frame p q} (h : Reach (onFrames F) y z) (hz : hits z) : hits y := by
    obtain ⟨w,lo,hi,j,hj⟩ := hz
    exact ⟨w,lo,hi,j,h.trans hj⟩
  have hq : 65 ≤ q := by have := C.q_eq; have := C.large; omega
  have endHits (w : ℕ) (lo : 1 ≤ w) (hi : w < q) (j : Fin 4) :
      hits (lastFrame m C.special.K C.special.E (slotPoint w j.val)) := by
    obtain ⟨w',lo',hi',j',he⟩ := route_legal (boundaryCase p) hq lo hi j.val
    exact ⟨w',lo',hi',j', he ▸ lastFirst w j.val lo hi j.isLt⟩
  have final (i : Fin (q - 1)) (j : Fin 4) : hits (fiber m (C.last i) (coord i) j) := by
    have h := endHits (i.val + 1) (by omega) (by have := i.isLt; omega) (toSlot j)
    simpa only [coord_last, slot_inverse] using h
  have hj : C.params.j < C.M := by have := C.params.index.2; have := C.q_eq; omega
  obtain ⟨za,zd⟩ := zero_rows_paths F C.two_ne C.params.index.1 hj C.params.a C.params.b C.v
    (fun Q h => C.has_zero switch hc h)
  obtain ⟨⟨row, s⟩, rfl⟩ := F.domain.surjective x
  rw [F.domain_val]
  rcases row with ⟨i,j⟩ | j | j | j
  · have atOne : decide (i.val = 0) = true → coord (p := p) i = 1 := by
      intro h
      simp [coord, of_decide_eq_true h]
    obtain ⟨_,drains⟩ := fiberRows_paths F C.two_ne (coord i) (switch (i.val+1))
      (C.first i) (C.last i) C.params.a C.params.b (C.middle i) (decide (i.val=0)) atOne za
      (fun Q h => C.has_ordinary switch hc i h)
    obtain ⟨t,ht⟩ := drains _ (List.get_mem (C.ordinary switch i) j) s
    exact pull ht (final i t)
  · obtain ⟨i,t,h⟩ := join_source C j s
    change hits ((C.joins j).dom (inverse m) s)
    rw [h]
    exact final i t
  · let L := Translations.paperLayout p C.M C.large
    let wa : ZMod p := ((q - 1 : ℕ) : ZMod p)
    let wb : ZMod p := Translations.w₀ p q
    obtain ⟨cross,drains⟩ := translation_paths F L C.special.E wa wb C.two_ne (by omega)
      (fun j => C.has_translation switch hc j)
    have hb (t : Fin 4) : hits (fiber m C.special.E wb t) :=
      ⟨Translations.w₀ p q, (w₀_bounds C).1, (w₀_bounds C).2, toSlot t,
        by rw [at_w₀ C]⟩
    change hits ((Translations.row m L C.special.E wa wb j).dom (inverse m) s)
    rcases translation_source (m := m) L C.special.E wa wb j s with ⟨i,t,h⟩ | ⟨t,h⟩
    · obtain ⟨u,hu⟩ := drains i t
      rw [h]
      exact pull hu (hb u)
    · rw [h]
      exact pull (cross t) (hb _)
  · let i : Fin (q - 1) := ⟨0, by omega⟩
    have cw : coord (p := p) i = 1 := by simp [coord,i]
    obtain ⟨t,ht⟩ := zd _ (List.get_mem C.zeros j) s
    have tailHas (Q) (h : Q ∈ toLast m 1 (switch 1) C.params.b (C.middle i) (C.last i)) :
        HasRow F Q := by
      apply C.has_ordinary switch hc i
      simpa [Construction.ordinary, fiberRows, i, coord] using
        (List.mem_cons_of_mem (canonical m (C.first i) C.params.a 1 false) h)
    have rest := (toLast_paths F C.two_ne 1 (switch 1) C.params.b (C.middle i) (C.last i)
      tailHas).1 t
    apply pull (ht.trans rest)
    simpa only [cw] using final i _

end BipartiteKneser.FamilyDrain
