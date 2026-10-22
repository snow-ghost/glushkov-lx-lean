import LRX.ExteriorGapRecenter

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Every two-component cursor pair has a sharp original-target word or the
true peak geometry. Both internal and exterior gaps are paid. -/
theorem two_component_sharp_or_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      (start ≠ finish ∧ JoinedPositiveArcs p hc start finish) := by
  rcases two_component_sharp_or_peak_or_outer hn p hmaj hc root hlarge start finish with hw | hp | ho
  · exact Or.inl hw
  · exact Or.inr hp
  · exact Or.inl (two_component_exterior_sharp_word hn p hmaj hc root hlarge start finish ho)

/-- Necessary bounds for an unpaid two-component peak in the original
maximal cut. All counts, energy and peak are taken from the actual map. -/
theorem two_component_unpaid_peak_bounds (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc) :
    n-p.support.card ≤ 5 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 7 ∧
      sourceHalfPeak p ≤ 10 := by
  classical
  let f := n-p.support.card
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have hf : f ≤ 5 := by
    by_contra hh
    have hpay := two_component_peak_paid_of_six_fixed hn p hmaj hmax hc (by
      change 6 ≤ f
      omega)
    omega
  have haf : (isolatedVertices p).card ≤ f := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB : bridgeBudget (componentBridges p hc) ≤ 5 := by
    by_cases ha : (isolatedVertices p).card=0
    · have hb := component_bridge_isolated_budget p hc
      omega
    · have hb := maximal_cut_bridge_strict_budget hn p hmax hc (by omega) (by omega)
      omega
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ sourceHalfPeak p := moved_global_peak_positive (sourceTarget p).symm u hum
  have hprice := peak_activity_bound hn p hmaj hc (by omega)
  change peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+1-
    (sourceHalfPeak p : ℤ)-(2*eps+(n%2 : ℕ)-(f : ℤ)) at hprice
  have hcredit := canonical_activity_credit_nonneg p hmaj
  change 0 ≤ 2*eps+(n%2 : ℕ)-(f : ℤ) at hcredit
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  change f ≤ 5 ∧ eps ≤ 7 ∧ sourceHalfPeak p ≤ 10
  omega

/-- Complete reduction of t=1 to its bounded-parameter unpaid peak. It does
not bound n and does not assert that the remaining peak is impossible. -/
theorem two_component_sharp_or_bounded_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      n-p.support.card ≤ 5 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 7 ∧
      sourceHalfPeak p ≤ 10) := by
  rcases two_component_sharp_or_peak hn p hmaj hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · by_cases hpay : peakExcess p hc ≤ 0
    · exact Or.inl (joined_peak_word_of_nonpositive_excess (by omega) p hc (by omega)
        start finish hp.1 hp.2 hpay)
    · have hpos : 1 ≤ peakExcess p hc := by omega
      exact Or.inr ⟨hp.1,hp.2,hpos,two_component_unpaid_peak_bounds (by omega) p hmaj hmax hc hpos⟩

#print axioms two_component_sharp_or_peak
#print axioms two_component_unpaid_peak_bounds
#print axioms two_component_sharp_or_bounded_peak
end LRX.FiniteCuts
