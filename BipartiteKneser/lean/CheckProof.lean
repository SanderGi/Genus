import BipartiteKneser
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Declaration linting, axiom audit, and a negative control for the face equations -/

#lint in BipartiteKneser
#lint in KneserConstruction
#lint in KneserWitnessData

open BipartiteKneser BipartiteKneser.Exceptional

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``optimalRotation_of_prime, ``exists_optimalRotation_gt,
      ``optimalRotation_of_lt_131, ``optimal_of_quadrangulation,
      ``Interval.realizes_iff_of_five, ``euler_bound] do
    let extra := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "{decl} uses unexpected axioms {extra}"

/- Check the public theorem type independently of its construction. -/
example : ∀ h : Nat, h.Prime → 3 < h → h % 8 = 3 → OptimalRotation h :=
  fun _ => optimalRotation_of_prime

/- Exchanging the first two labels preserves coverage but destroys a face. -/
private def swapFirst (i : Fin 36) : Fin 36 := if i = 0 then 1 else if i = 1 then 0 else i

private def altered : BaseCycle 11 5 36 :=
  { cycle11 with label := fun i => cycle11.label (swapFirst i)
                 index := fun s => swapFirst (cycle11.index s) }

example : altered.Covers := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [Prod.forall]
    decide +kernel

example : ∃ i, altered.checkFace false i = false := by decide +kernel
