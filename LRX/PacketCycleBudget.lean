import LRX.ZeroGapCycleRoots
import LRX.ZeroGapEvents
import Mathlib

/-! Reflection-rank and packet-cycle bounds come from the actual sorting
events. Combined with majorization they pay the two-arc numerical budget. -/
namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem reflection_rank_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    (p.support.card : ℤ)+(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      (∑ i : Fin n, |d i|)+((p⁻¹).cycleFactorsFinset.card : ℤ) := by
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,htravel⟩ := sorting_events hd hshort
  have h := cycle_root_count hprod
  omega


#print axioms reflection_rank_inversion_bound
end LRX.ZeroGap

namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]


end LRX.FiniteGaps
