import LRX.FiniteShallowMatching
import LRX.FixedCountReflection
import LRX.ShiftedAdjacentPairs
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Equality in the capacity bound gives reflection once the cut is at a fixed
endpoint residue. All pair and fixed-count premises are derived from the lift. -/
theorem inherited_capacity_equality_reflection_at_zero
    {p : State n} {phase : ℤ} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p phase d) (h : ℤ)
    (hparity : (n : ℤ)=2*h+1 ∨ (n : ℤ)=2*h+2)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (hupper : ∀ i, d i ≤ h)
    (hinheritNeg : ∀ i, d i= -h → original i= -h)
    (hinheritPos : ∀ i, d i=h → original i=h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1))
    (hzero : shiftedLiftPermutation p phase h 0=0) :
    ∀ i, shiftedLiftPermutation p phase h i= -i := by
  have hh : 2*h ≤ (n : ℤ) := by omega
  obtain ⟨hs,_,_,hpairs⟩ := inherited_capacity_equality_pairs horiginal hmaj hd h hh hband hinheritNeg heq
  let q := shiftedLiftPermutation p phase h
  have hinv : Function.Involutive q := involutive_of_cycles_are_swaps q hpairs
  have hnc : NoncrossingPairs q := by
    intro a b c d hab hbc hcd hac
    exact inherited_capacity_equality_noncrossing horiginal hmaj hd h hh hband hinheritNeg heq
      a b c d hab hbc hcd hac
  have hf := fixed_positions_card q
  change (q.support.card : ℤ)=2*h at hs
  rcases hparity with hodd | heven
  · have hc : (fixedPositions q).card=1 := by omega
    exact fixed_count_one_reflection q hinv hnc hzero hc
      (shifted_unique_adjacent_of_inherited_extremes hmaj hd h hodd hband hinheritPos hinv)
  · have hc : (fixedPositions q).card=2 := by omega
    exact fixed_count_two_reflection q hinv hnc hzero hc
      (shifted_no_adjacent_of_narrow_strip hd h hband hupper (by omega) hinv)

#print axioms inherited_capacity_equality_reflection_at_zero
end LRX.FiniteCuts
