import LX.DirectedLiftLower
import LX.Small6Exact

namespace LX.DirectedLowerRegression
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.LiftedModel LRX.AffineLift

def trialDisplacement : Fin 6 → ℤ := ![1,-2,-2,1,-1,3]

theorem trial_lift : IsLift Small6.farthest 6 trialDisplacement := by
  have hf : ∀ i : Fin 6,Small6.farthest (![1,5,0,4,3,2] i)=i := by
    decide +kernel
  have hi (i : Fin 6) : Small6.farthest.symm i=(![1,5,0,4,3,2] : Fin 6 → Fin 6) i := by
    apply Small6.farthest.injective
    rw [Equiv.apply_symm_apply]
    exact (hf i).symm
  unfold IsLift
  simp_rw [hi]
  unfold Int.ModEq
  decide +kernel

theorem trial_budget : ∀ i : Fin 6,
    (6 : ℤ)*(i.val-1 : ℕ)-5*((i : ℤ)+trialDisplacement i) ≤ 6 := by
  decide +kernel

theorem trial_price :
    (inversionCount (fun i : Fin 6 => (i : ℤ)+trialDisplacement i) : ℤ)+6=12 := by
  decide +kernel

/-- A concrete balanced lift satisfies all endpoint constraints at price
12, while every literal word for this permutation has length at least 18.
Thus those constraints alone cannot prove the conjectured lower bound. -/
theorem endpoint_constraints_insufficient : ¬ (∀ c : ℤ,∀ d : Fin 6 → ℤ,
    IsLift Small6.farthest c d → 0 ≤ c →
    (∀ i : Fin 6,(6 : ℤ)*(i.val-1 : ℕ)-5*((i : ℤ)+d i) ≤ c) →
    18 ≤ (inversionCount (fun i : Fin 6 => (i : ℤ)+d i) : ℤ)+c) := by
  intro h
  have hb := h 6 trialDisplacement trial_lift (by norm_num) trial_budget
  rw [trial_price] at hb
  omega

theorem literal_word_lower (w : List Letter) (hw : eval w=Small6.farthest) :
    18 ≤ w.length := by
  have hb := potential_word_bound Small6.score (by
    intro p a
    simpa only [LRX.decode_encode] using Small6.potential_edges (LRX.encode p) a) 1 w
  simpa only [one_mul,hw,Small6.farthest_score,Small6.potential_zero,zero_add] using hb

#print axioms endpoint_constraints_insufficient
#print axioms literal_word_lower
end LX.DirectedLowerRegression
