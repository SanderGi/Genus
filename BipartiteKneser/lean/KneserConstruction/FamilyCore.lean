module

public import KneserConstruction.Multipliers

/-!
# Rotation quadruples and their induced permutation

The row address is separate from the four slots inside a row. Completeness is a
pair of bijections onto the actual connection set, so a later iteration proof
can use the row equations for the permutation without performing a search.
-/

@[expose] public section

namespace BipartiteKneser.Family

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- A dart label in the connection set. -/
abbrev Label (m : Multipliers p q) := {s : Frame p q // separated m.power s = true}

/-- Inversion in the affine group. -/
def inverse (m : Multipliers p q) (s : Frame p q) : Frame p q :=
  (-(m.power (-s.2) * s.1), -s.2)

/-- First bit selects an inverse pair, second bit selects its orientation. -/
abbrev Slot := Bool × Bool

/-- The four entries in the paper's order Q(a,b;c,d). -/
structure Quad (α : Type*) where
  /-- Representative of the first domain inverse pair. -/
  a : α
  /-- Representative of the second domain inverse pair. -/
  b : α
  /-- Image of the inverse of the first domain representative. -/
  c : α
  /-- Image of the first domain representative. -/
  d : α

/-- Source label of an assignment. -/
def Quad.dom {α : Type*} (inv : α → α) (Q : Quad α) : Slot → α
  | (false, false) => Q.a
  | (false, true) => inv Q.a
  | (true, false) => Q.b
  | (true, true) => inv Q.b

/-- Target label of the corresponding assignment. -/
def Quad.ran {α : Type*} (inv : α → α) (Q : Quad α) : Slot → α
  | (false, false) => Q.d
  | (false, true) => Q.c
  | (true, false) => inv Q.d
  | (true, true) => inv Q.c

/-- A complete admissible family with row index type `ι`. -/
structure Complete (m : Multipliers p q) (ι : Type*) where
  /-- The quadruple written at each row index. -/
  row : ι → Quad (Frame p q)
  closed (i : ι) : compose m.power (row i).a (row i).c = compose m.power (row i).d (row i).b
  /-- Bijection assigning each source slot to its connection label. -/
  domain : (ι × Slot) ≃ Label m
  /-- Bijection assigning each target slot to its connection label. -/
  range : (ι × Slot) ≃ Label m
  domain_val (i : ι) (s : Slot) : (domain (i,s)).val = Quad.dom (inverse m) (row i) s
  range_val (i : ι) (s : Slot) : (range (i,s)).val = Quad.ran (inverse m) (row i) s

namespace Complete

variable {m : Multipliers p q} {ι : Type*} (F : Complete m ι)

/-- The assembled rotation on separated affine frames. -/
def rho : Equiv.Perm (Label m) := F.domain.symm.trans F.range

/-- All four assignments, before forgetting connection-set membership. -/
@[simp] theorem rho_domain (i : ι) (s : Slot) :
    F.rho (F.domain (i,s)) = F.range (i,s) := by simp [rho]

/-- All four assignments in affine coordinates. -/
theorem rho_row (i : ι) (s : Slot) :
    (F.rho (F.domain (i,s))).val = Quad.ran (inverse m) (F.row i) s := by
  rw [F.rho_domain, F.range_val]

end Complete
end BipartiteKneser.Family
