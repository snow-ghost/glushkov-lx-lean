import LX.DirectedTokenLower

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

/-- Simultaneous endpoint, inversion and token constraints extracted
from the same arbitrary word. These are necessary conditions only. -/
theorem word_lower_data (hn : 2 ≤ n) (w : List Letter) :
    ∃ c : ℤ,∃ d : Fin n → ℤ,IsLift (eval w) c d ∧ 0 ≤ c ∧
      (inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+c ≤ (w.length : ℤ) ∧
      ∀ i : Fin n,(n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*((i : ℤ)+d i) ≤ c := by
  let s := run (w.map Letter.toLRX) (initial (n := n))
  refine ⟨s.cursor,(fun i => s.position i-(i : ℤ)),word_endpoint_lift hn w,?_,?_,?_⟩
  · dsimp only [s]
    rw [cursor_eq_left_count]
    positivity
  · simpa only [add_sub_cancel] using word_inversion_cursor_lower hn w
  · intro i
    simpa only [add_sub_cancel] using word_cursor_lower hn w i

#print axioms word_endpoint_lift
#print axioms word_lower_data
end LX.DirectedTokenLower
