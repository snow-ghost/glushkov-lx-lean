import LRX.ClockwiseLiftCount
import LRX.FiniteCrossPairCount
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem clockwise_pair_quotient (p : State n) (i j : Fin n) :
    (clockwiseRepresentative p j-clockwiseRepresentative p i)/(n : ℤ)=
      (if (p j).val < (p i).val then (-1 : ℤ) else 0)+
        descendingIndicator p j-descendingIndicator p i := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hi := (p i).isLt
  have hj := (p j).isLt
  unfold clockwiseRepresentative descendingIndicator
  split_ifs <;> apply PeriodicBuffer.quotient_eq_of_bounds hn <;> omega

/-- The affine pair contribution is a finite inversion, plus a cross-pair
charge, minus twice the weighted finite inversion correction. -/
theorem clockwise_inversion_term (p : State n) (i j : Fin n) :
    (ZeroGap.inversionTerm (clockwiseRepresentative p) i j : ℤ)=
      inversionIndicator p i j+crossPairIndicator p i j-
        2*(inversionIndicator p i j*(descendingIndicator p j-descendingIndicator p i)) := by
  by_cases hij : i < j
  · rw [ZeroGap.inversionTerm, if_pos hij, clockwise_pair_quotient]
    unfold inversionIndicator crossPairIndicator descendingIndicator
    have hijval : i.val < j.val := hij
    simp only [if_pos hij]
    split_ifs <;> norm_num <;> omega
  · have hnot : ¬i.val < j.val := hij
    simp [ZeroGap.inversionTerm, inversionIndicator, crossPairIndicator, hij, hnot]

/-- Formula (24), first for the canonical clockwise representative of any permutation. -/
theorem clockwise_inversion_count (p : State n) :
    (LiftedModel.inversionCount (clockwiseRepresentative p) : ℤ)=
      ((descendingPositions p).card : ℤ)*((n : ℤ)-(descendingPositions p).card)+
        (inversionNumber p : ℤ)-2*leftDepth p := by
  have hcast : (LiftedModel.inversionCount (clockwiseRepresentative p) : ℤ)=
      ∑ i, ∑ j, (ZeroGap.inversionTerm (clockwiseRepresentative p) i j : ℤ) := by
    simp only [LiftedModel.inversionCount, ZeroGap.inversionTerm, Nat.cast_sum]
  rw [hcast]
  simp_rw [clockwise_inversion_term, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [sum_inversion_indicator, sum_cross_pair_indicator, weighted_inversion_balance]
  ring

#print axioms clockwise_inversion_count
end LRX.FiniteCuts
