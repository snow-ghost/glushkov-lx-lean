import LRX.LiftedModel
import LX.WordMetric
import Mathlib

namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.LiftedModel LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every actual LX word provides a balanced lift with its paid cursor,
not an independently selected phase. -/
theorem word_endpoint_lift (hn : 2 ≤ n) (w : List Letter) :
    IsLift (eval (n := n) w) (run (w.map Letter.toLRX) (initial (n := n))).cursor
      (fun i => (run (w.map Letter.toLRX) (initial (n := n))).position i-(i : ℤ)) := by
  let s := run (w.map Letter.toLRX) (initial (n := n))
  have hs : Aligned s := run_aligned hn _ initial_aligned
  have he : LRX.PhysicalModel.visible s.physical=eval w := by
    dsimp only [s]
    rw [run_physical,LRX.PhysicalModel.visible_run]
    change 1*eval w=eval w
    exact one_mul _
  refine ⟨displacement_balanced _,?_⟩
  intro i
  change Int.ModEq (n : ℤ) ((i : ℤ)+(s.position i-(i : ℤ)))
    (((eval w).symm i : ℤ)+s.cursor)
  apply (cast_eq_iff_modEq _ _).mp
  simp only [add_sub_cancel,Int.cast_add]
  rw [hs.2,hs.1]
  have hv := congrArg (fun p : State n => p ((eval w).symm i)) he
  rw [LRX.PhysicalModel.visible_apply,Equiv.apply_symm_apply] at hv
  have hh := congrArg s.physical.tokens.symm hv
  simpa using hh.symm


#print axioms word_endpoint_lift
end LX.DirectedTokenLower
