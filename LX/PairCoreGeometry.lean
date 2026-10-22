import LX.AnchorReserveRigidity
import LRX.CycleDefectMonotonicity
import LRX.FiniteShallowMatching

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
  LRX.PrunedLift.permutation q (positions q) (positions_invariant q)

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

theorem permutation_zero_defect (q : State n) (hq : LRX.FiniteCuts.cycleDefect q=0) :
    LRX.FiniteCuts.cycleDefect (permutation q)=0 :=
  LRX.FiniteCuts.zero_defect_pruned_factor q (positions q) (positions_invariant q) hq

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
    _ = ∑ g ∈ e.cycleFactorsFinset,g.support.card := (LRX.FiniteCuts.cycle_support_card_sum e).symm
    _ = ∑ _g ∈ e.cycleFactorsFinset,2 := Finset.sum_congr rfl hsize
    _ = _ := by simp [e,mul_comm]

/-- Noncrossing is inherited from zero defect through the actual pruned
factor. Involutivity alone would not justify this conclusion. -/
theorem permutation_noncrossing (q : State n) (hq : LRX.FiniteCuts.cycleDefect q=0) :
    LRX.FiniteCuts.NoncrossingPairs (permutation q) := by
  have hs := permutation_support_card q
  have hz := permutation_zero_defect q hq
  have hdef : (∑ i, |LRX.FiniteCuts.displacement (permutation q) i|)-
      (LRX.FiniteCuts.inversionNumber (permutation q) : ℤ)=
      ((permutation q).cycleFactorsFinset.card : ℤ) := by
    unfold LRX.FiniteCuts.cycleDefect at hz
    rw [hs] at hz
    push_cast at hz
    omega
  intro a b c d hab hbc hcd hac
  exact LRX.FiniteCuts.finite_shallow_matching_noncrossing (permutation q)
    (permutation q).cycleFactorsFinset.card hs hdef a b c d hab hbc hcd hac

/-- Original transposition arrows cannot alternate around the linear cut. -/
theorem original_pairs_noncrossing (q : State n) (hq : LRX.FiniteCuts.cycleDefect q=0)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : q a=c) (hca : q c=a) (hbd : q b=d) : q d ≠ b := by
  intro hdb
  have ha : permutation q a=c := by simp [hac,hca]
  have hb : permutation q b=d := by simp [hbd,hdb]
  exact permutation_noncrossing q hq a b c d hab hbc hcd ha hb

/-- Every removed position belongs to a genuine cycle longer than two.
This converts cycle mass into a bound on the exceptional physical positions. -/
theorem removed_positions_card (q : State n) :
    (positions q)ᶜ.card ≤
      ∑ g ∈ q.cycleFactorsFinset.filter (fun g => g.support.card ≠ 2),g.support.card := by
  classical
  let C := q.cycleFactorsFinset.filter (fun g => g.support.card ≠ 2)
  have hsub : (positions q)ᶜ ⊆ C.biUnion (fun g => g.support) := by
    intro i hi
    have hnot : q (q i) ≠ i := by simpa [positions] using hi
    have hni : q i ≠ i := by intro hh; apply hnot; rw [hh,hh]
    let g := q.cycleOf i
    have hg : g ∈ q.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hni)
    have hgi : g i=q i := Equiv.Perm.cycleOf_apply_self q i
    have hlong : g.support.card ≠ 2 := by
      intro hc
      obtain ⟨u,v,_,heq⟩ := Equiv.Perm.card_support_eq_two.mp hc
      have hgg : g (g i)=i := by rw [heq]; simp
      have hqq : g (g i)=q (q i) := by
        rw [hgi]
        exact Equiv.Perm.cycleOf_apply_apply_self q i
      exact hnot (hqq.symm.trans hgg)
    refine Finset.mem_biUnion.mpr ⟨g,Finset.mem_filter.mpr ⟨hg,hlong⟩,?_⟩
    exact Equiv.Perm.mem_support.mpr (by rw [hgi]; exact hni)
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

#print axioms permutation_support_card
#print axioms permutation_noncrossing
#print axioms original_pairs_noncrossing
#print axioms removed_positions_card
end LX.PairCore

namespace LX.AnchoredPhases
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem small_global_reserve_pair_core {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    LRX.FiniteCuts.NoncrossingPairs (LX.PairCore.permutation (permutation p a)) :=
  LX.PairCore.permutation_noncrossing _ (small_global_reserve_rigidity ha hsmall).1

/-- A genuine noncrossing involution agrees with the normalized input at all
but six positions. Neither the matching nor the exceptional set is assumed. -/
theorem small_global_reserve_pair_core_structure {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    ∃ e : State n,∃ B : Finset (Fin n),Function.Involutive e ∧
      LRX.FiniteCuts.NoncrossingPairs e ∧ B.card ≤ 6 ∧
      ∀ i ∉ B,e i=permutation p a i := by
  refine ⟨LX.PairCore.permutation (permutation p a),(LX.PairCore.positions (permutation p a))ᶜ,
    LX.PairCore.permutation_involutive _,small_global_reserve_pair_core ha hsmall,?_,?_⟩
  · exact (LX.PairCore.removed_positions_card _).trans (small_global_reserve_nonpair_mass ha hsmall)
  · intro i hi
    have hh : permutation p a (permutation p a i)=i := by
      simpa [LX.PairCore.positions] using hi
    simp only [LX.PairCore.permutation_apply,ite_eq_left hh]

#print axioms small_global_reserve_pair_core
#print axioms small_global_reserve_pair_core_structure
end LX.AnchoredPhases
