import LX.ReflectionConjecture
import LX.OddUnitPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Extract the adjacent fixed pair directly from the zero-reserve source;
no unpaid-word assumption or auxiliary numerical constant is used. -/
theorem odd_zero_reserve_adjacent_fixed (p : State n) (a : Fin n)
    (hn7 : 7 ≤ n) (hn : n=2*height p a+3)
    (hm : Majorized (displacement p a)) (hz : anchorReserve p a=0) :
    ∃ u : Fin n,permutation p a u=u ∧ permutation p a (u+1)=u+1 := by
  have hd := is_lift p a
  have heq : (LRX.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+displacement p a i) : ℤ)=
      (height p a : ℤ)*((n : ℤ)-height p a-1) := by
    change (inversions (displacement p a) : ℤ)=_
    unfold anchorReserve at hz
    omega
  obtain ⟨hs,hc,hdef,hpairs⟩ := inherited_capacity_equality_pairs hd.1 hm hd
    (height p a : ℤ) (by omega) (displacement_band p a) (fun _ hi => hi) heq
  simp only [shifted_anchor_permutation] at hs hc hdef hpairs
  have hinv := involutive_of_cycles_are_swaps (permutation p a) hpairs
  have hnc : NoncrossingPairs (permutation p a) := by
    intro i j k l hij hjk hkl hik
    have ht := inherited_capacity_equality_noncrossing hd.1 hm hd
      (height p a : ℤ) (by omega) (displacement_band p a) (fun _ hi => hi) heq
    simpa only [shifted_anchor_permutation] using ht i j k l hij hjk hkl (by
      simpa only [shifted_anchor_permutation] using hik)
  have hsupport : 4 ≤ (permutation p a).support.card := by omega
  exact LX.MatchingGeometry.exists_adjacent_fixed (permutation p a) hinv hnc hsupport
    (three_fixed_matching_no_cyclic_adjacent (by omega) p a hm hn hinv)
    (three_fixed_matching_unique_cyclic_gap_two (by omega) p a hm hn hinv)

#print axioms odd_zero_reserve_adjacent_fixed
end LX.AnchoredPhases
