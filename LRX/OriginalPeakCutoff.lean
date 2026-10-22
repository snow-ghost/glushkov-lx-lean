import LRX.NormalizedPeakReserve
import LRX.ActualUnpaidPeakCutoff

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- For the actual original maximal-cut route, only the first C8 estimate
remains an unproved budget premise. Every other cutoff hypothesis is derived.
This conditional reduction is not a proof of first C8 or of sharp routing. -/
theorem original_peak_cutoff_of_first_C8 (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (hpos : 1 ≤ peakExcess p hc)
    (hfirst : let q := localTarget p 0 (componentLeft p root)
      let t : ℤ := (nontrivialSuffixComponents q (componentSet p root).card).card
      let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|)
      peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+t-
        (sourceHalfPeak q : ℤ)-(2*eps+(n%2 : ℕ)-((n-q.support.card : ℕ) : ℤ))) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577 := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let B : ℤ := bridgeBudget (componentBridges p hc)
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hlarge' : (n+1)/2 < (componentSet q 0).card := by omega
  have hproper := component_card_lt_of_multiple_roots p (by omega) root
  have hproper' : (componentSet q 0).card < n := by omega
  have ht' : 2 ≤ (nontrivialSuffixComponents q (componentSet q 0).card).card := by
    rw [hzero]
    exact ht
  have hcount := component_cut_external_count p root hsize
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have htk : (nontrivialSuffixComponents q L).card=k := by omega
  have hB := maximal_bridge_bounds_at_component_cut hn p hmax hc hk root hsize
  have hB0 : (singletonSuffixComponents q (componentSet q 0).card).card=0 →
      B ≤ ((nontrivialSuffixComponents q (componentSet q 0).card).card : ℤ) := by
    rw [hzero,htk]
    intro ha
    exact hB.1 (by exact_mod_cast ha)
  have hB1 : 1 ≤ (singletonSuffixComponents q (componentSet q 0).card).card →
      B ≤ ((singletonSuffixComponents q (componentSet q 0).card).card : ℤ)+
        ((nontrivialSuffixComponents q (componentSet q 0).card).card : ℤ)-1 := by
    rw [hzero,htk]
    intro ha
    exact hB.2 (by exact_mod_cast ha)
  suffices hres : (nontrivialSuffixComponents q (componentSet q 0).card).card ≤ 7 ∧
      n/2 ≤ 288 ∧ n ≤ 577 by
    simpa only [hzero] using hres
  apply actual_unpaid_peak_cutoff q hqm hlarge' hproper' ht' B hB0 hB1
  · dsimp only
    rw [hzero]
    exact hpos.trans hfirst
  · have hb := normalized_peak_reserve_bound hn p hmaj hc hk root hlarge
    have hh := hpos.trans hb
    dsimp only at hh ⊢
    rw [hzero]
    simpa only [q,L,B,Nat.cast_sum] using hh

#print axioms original_peak_cutoff_of_first_C8
end LRX.FiniteCuts
