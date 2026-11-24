import BipartiteKneser.Interval
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.Card

/-!
# Section 7 boundary labels

The four labels of an outside fiber occur in the order (++),(+−),(−+),(−−).
The six entry labels follow in the order of the two triples of Proposition 6.7.
All permutations of triples are stored in the forward direction.
-/

namespace BipartiteKneser.Boundary

inductive Case where
  | one | two
  deriving DecidableEq, Repr

def count : Case → Nat | .one => 12 | .two => 14

def size (c : Case) := 4 * count c + 6

abbrev Label (c : Case) := Fin (size c)
abbrev Pattern (c : Case) := Fin (2 ^ count c)

instance (c : Case) : NeZero (size c) := ⟨by cases c <;> decide⟩

/-- Four packed target indices, one byte per post-bijection sign pair.
These tables are related to the symbolic arithmetic in `normalize_step`. -/
def routes : Case → Array Nat
  | .one => #[0x30332f2c, 0x34310b08, 0x5062a29, 0x24270a09, 0x191a1714, 0x1d1e1b18,
      0x21221f1c, 0x25262320, 0x10130704, 0x2d2e2b28, 0x15163235, 0x2030001]
  | .two => #[0x383b0605, 0xd0e0b08, 0x3c390f0c, 0x4070300, 0x34372b28, 0x1d1e1b18,
      0x21221f1c, 0x25262320, 0x292a2724, 0x2c2f0201, 0x35360a09,
      0x191a3a3d, 0x14172e2d, 0x32333031]

/-- Bit 1 encodes a negative exponent, bit 0 a negative coordinate. -/
def lastSlot (i slot : Nat) (missing switch : Bool) : Nat :=
  let e := slot.testBit 1
  let t := slot.testBit 0
  let t' := if i = 0 then !e else t
  let e' := if i = 0 then (if missing then e ^^ t else !t)
            else e ^^ (!missing && t)
  2 * (e' ^^ switch).toNat + t'.toNat

def routeIndex (c : Case) (i slot : Nat) : Nat :=
  ((routes c)[i]! >>> (8 * slot)) % 256

/-- Index of exit port j in the same ordering as the entries. -/
def exitIndex (c : Case) (j : Nat) : Nat :=
  (if c = .one then 12 else 16) + (#[0, 2, 6, 3, 1, 5] : Array Nat)[j]!

def transferIndex (p r : Interval.Perm) (j : Nat) : Nat :=
  (if j < 3 then 0 else 3) +
    (Interval.image (if j < 3 then p else r) (Fin.ofNat 3 j)).val

def nextIndex (c : Case) (chars mask : Nat) (p r : Interval.Perm) (x : Nat) : Nat :=
  if x < 4 * count c then
    let i := x / 4
    routeIndex c i (lastSlot i (x % 4) (chars.testBit i) (mask.testBit i))
  else exitIndex c (transferIndex p r (x - 4 * count c))

def step (c : Case) (chars : Pattern c) (mask : Nat) (p r : Interval.Perm)
    (x : Label c) : Label c := Fin.ofNat _ (nextIndex c chars.val mask p r x.val)

/-- Count parity in precisely the low bits naming retained fibers. -/
def positiveParity (c : Case) (chars : Pattern c) : Bool :=
  Interval.parity ((List.range (count c)).map chars.val.testBit)

def choices : Case → List Nat
  | .one => [0, 1, 2, 3, 4, 5, 32, 33, 34, 35, 82, 98]
  | .two => [0, 1, 3, 4, 5, 32, 33, 36, 37, 38, 64, 65, 67, 68, 69, 96, 97, 100,
      101, 102, 192, 193, 196, 197, 256, 257, 260, 261, 384, 385, 388, 389]

end BipartiteKneser.Boundary
