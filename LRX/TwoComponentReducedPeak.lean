import LRX.FourFixedPeakPayment

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The exact active-support floor improves the square activity bound when
there are three fixed positions and n is even. -/
theorem three_fixed_even_energy_reserve (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hf : n-p.support.card=3) (hp : n%2=0) :
    4 ≤ ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hmass := ZeroGap.active_mass_cap hd hmaj
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hk : ((p.support.card/2 : ℕ) : ℤ)=((n/2 : ℕ) : ℤ)-2 := by omega
  have hn : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  rw [hk,hn] at hmass
  rw [hn]
  nlinarith only [hmass]

/-- After the actual f=4 geometric payment, the remaining two-component
peak has f<=3, epsilon<=2 and U<=4. There is still no bound on n. -/
theorem two_component_unpaid_peak_reduced_bounds (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    n-p.support.card ≤ 3 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 2 ∧
      sourceHalfPeak p ≤ 4 := by
  classical
  let f := n-p.support.card
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have hbds := two_component_unpaid_peak_tight_bounds (by omega) p hmaj hmax hc hpos
  have hf3 : f ≤ 3 := by
    by_contra hh
    have hfbound : f ≤ 4 := hbds.1
    have hf4 : n-p.support.card=4 := by change f=4; omega
    have hpay := two_component_peak_paid_of_four_fixed hn p hmaj hmax hc root hlarge hf4
    omega
  have haf : (isolatedVertices p).card ≤ f := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB2 := two_component_twice_bridge_budget (by omega) p hmax hc
  have hB : bridgeBudget (componentBridges p hc) ≤ 2 := by omega
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ sourceHalfPeak p := moved_global_peak_positive (sourceTarget p).symm u hum
  have hprice := peak_activity_bound (by omega) p hmaj hc (by omega)
  change peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+1-
    (sourceHalfPeak p : ℤ)-(2*eps+(n%2 : ℕ)-(f : ℤ)) at hprice
  have hp0 : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have he3 : eps ≤ 3 := by omega
  have he2 : eps ≤ 2 := by
    by_contra hh
    have heq : eps=3 := by omega
    have hf : n-p.support.card=3 := by change f=3; omega
    have hp : n%2=0 := by omega
    have h := three_fixed_even_energy_reserve p hmaj hf hp
    change 4 ≤ eps at h
    omega
  exact ⟨hf3,he2,hbds.2.2⟩

theorem two_component_sharp_or_reduced_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      n-p.support.card ≤ 3 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 2 ∧
      sourceHalfPeak p ≤ 4) := by
  rcases two_component_sharp_or_peak hn p hmaj hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · by_cases hpay : peakExcess p hc ≤ 0
    · exact Or.inl (joined_peak_word_of_nonpositive_excess (by omega) p hc (by omega)
        start finish hp.1 hp.2 hpay)
    · have hpos : 1 ≤ peakExcess p hc := by omega
      exact Or.inr ⟨hp.1,hp.2,hpos,two_component_unpaid_peak_reduced_bounds hn p hmaj hmax hc root hlarge hpos⟩

#print axioms three_fixed_even_energy_reserve
#print axioms two_component_unpaid_peak_reduced_bounds
#print axioms two_component_sharp_or_reduced_peak
end LRX.FiniteCuts
