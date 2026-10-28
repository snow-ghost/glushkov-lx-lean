import LX.CycleDefectMonotonicity
import LX.FiniteShallowMatching
import LX.LinearMatchingGeometry
import LX.WordMetric
import Mathlib

namespace LX.PairCore
open scoped BigOperators
variable {n : ℕ}

/-- Retain the fixed points and transposition cycles of the actual finite
permutation, without choosing a new matching. -/
def positions (q : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => q (q i)=i)

theorem positions_invariant (q : State n) (i : Fin n) :
    q i ∈ positions q ↔ i ∈ positions q := by
  simp only [positions,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hh
    exact q.injective hh
  · exact congrArg q

def permutation (q : State n) : State n :=
  LX.Core.PrunedLift.permutation q (positions q) (positions_invariant q)

@[simp] theorem permutation_apply (q : State n) (i : Fin n) :
    permutation q i=if q (q i)=i then q i else i := by
  simp [permutation,positions]

theorem permutation_involutive (q : State n) : Function.Involutive (permutation q) := by
  intro i
  by_cases hi : q (q i)=i
  · have hj := congrArg q hi
    simp only [permutation_apply,ite_eq_left hi,ite_eq_left hj]
    exact hi
  · simp only [permutation_apply,ite_eq_right hi]

theorem permutation_zero_defect (q : State n) (hq : LX.Core.FiniteCuts.cycleDefect q=0) :
    LX.Core.FiniteCuts.cycleDefect (permutation q)=0 :=
  LX.Core.FiniteCuts.zero_defect_pruned_factor q (positions q) (positions_invariant q) hq

theorem permutation_support_card (q : State n) :
    (permutation q).support.card=2*(permutation q).cycleFactorsFinset.card := by
  classical
  let e := permutation q
  have he : e^2=1 := by
    apply Equiv.ext
    intro i
    change e (e i)=i
    exact permutation_involutive q i
  have htypes := (Equiv.Perm.pow_prime_eq_one_iff (p := 2)).mp he
  have hsize (g : State n) (hg : g ∈ e.cycleFactorsFinset) : g.support.card=2 := by
    apply htypes
    unfold Equiv.Perm.cycleType
    exact Multiset.mem_map.mpr ⟨g,hg,rfl⟩
  calc
    _ = ∑ g ∈ e.cycleFactorsFinset,g.support.card := (LX.Core.FiniteCuts.cycle_support_card_sum e).symm
    _ = ∑ _g ∈ e.cycleFactorsFinset,2 := Finset.sum_congr rfl hsize
    _ = _ := by simp [e,mul_comm]

/-- Noncrossing is inherited from zero defect through the actual pruned
factor. Involutivity alone would not justify this conclusion. -/
theorem permutation_noncrossing (q : State n) (hq : LX.Core.FiniteCuts.cycleDefect q=0) :
    LX.Core.FiniteCuts.NoncrossingPairs (permutation q) := by
  have hs := permutation_support_card q
  have hz := permutation_zero_defect q hq
  have hdef : (∑ i, |LX.Core.FiniteCuts.displacement (permutation q) i|)-
      (LX.Core.FiniteCuts.inversionNumber (permutation q) : ℤ)=
      ((permutation q).cycleFactorsFinset.card : ℤ) := by
    unfold LX.Core.FiniteCuts.cycleDefect at hz
    rw [hs] at hz
    push_cast at hz
    omega
  intro a b c d hab hbc hcd hac
  exact LX.Core.FiniteCuts.finite_shallow_matching_noncrossing (permutation q)
    (permutation q).cycleFactorsFinset.card hs hdef a b c d hab hbc hcd hac


#print axioms permutation_support_card
#print axioms permutation_noncrossing
end LX.PairCore

namespace LX.AnchoredPhases
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases
