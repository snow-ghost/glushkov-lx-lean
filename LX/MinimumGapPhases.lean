import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A later equal-height phase forces the earlier fixed fiber to fit
inside their separation. This controls every phase except the least gap. -/
theorem smaller_gap_bounds_fixed (p : State n) (a b : Fin n)
    (hh : height p b=height p a) (hg : (b-p b).val < (a-p a).val) :
    (fixedPositions (permutation p a)).card ≤ (a-p a).val := by
  have hoff : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    rw [hoff,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hg.le)]
  have he := reanchor_height p a b
  have hcount : belowCount p a (cyclicOffset p a b).val=(cyclicOffset p a b).val := by omega
  have hf : (fixedPositions (permutation p a)).card ≤ belowCount p a (cyclicOffset p a b).val := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p a i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  omega


#print axioms smaller_gap_bounds_fixed
end LX.AnchoredPhases
