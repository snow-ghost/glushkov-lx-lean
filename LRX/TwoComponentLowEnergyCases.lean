import LRX.ZeroEnergyUnitPeak

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Unit energy reserve forces n=2 modulo 4 by the exact even energy. -/
theorem unit_energy_reserve_size_mod_four (p : State n)
    (heps : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1) :
    n%4=2 := by
  let m : ℤ := (n/2 : ℕ)
  obtain ⟨z,hz⟩ := canonical_energy_twice p
  have he : m*((n : ℤ)-m)-2*z=1 := by dsimp only [m]; linarith only [heps,hz]
  have hn : (n : ℤ)=2*m+(n%2 : ℕ) := by dsimp only [m]; omega
  obtain ⟨w,hw⟩ := Int.even_mul_succ_self m
  have hp : n%2=0 := by
    by_contra hh
    have hp1 : n%2=1 := by omega
    have he' := he
    rw [hn,hp1] at he'
    norm_num only [Nat.cast_one] at he'
    have hbad : 2*(w-z)=1 := by nlinarith only [he',hw]
    omega
  rw [hp] at hn
  norm_num only [Nat.cast_zero,add_zero] at hn
  rw [hn] at he
  have hn4 : (n : ℤ)=4*(w-z)-2 := by nlinarith only [he,hw,hn]
  omega

/-- Shared true activity information for an unpaid two-component peak. -/
theorem unpaid_two_component_activity (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc) :
    let f : ℤ := (n-p.support.card : ℕ)
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    let B : ℤ := bridgeBudget (componentBridges p hc)
    let U : ℤ := sourceHalfPeak p
    1 ≤ U ∧ 2*B ≤ f+2 ∧ U+(2*eps+(n%2 : ℕ)-f) ≤ 2*B ∧
      0 ≤ 2*eps+(n%2 : ℕ)-f := by
  classical
  have haf : (isolatedVertices p).card ≤ n-p.support.card := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB := two_component_twice_bridge_budget hn p hmax hc
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ sourceHalfPeak p := moved_global_peak_positive (sourceTarget p).symm u hum
  have hprice := peak_activity_bound hn p hmaj hc (by omega)
  have hcredit := canonical_activity_credit_nonneg p hmaj
  dsimp only at hprice ⊢
  exact ⟨by omega,by omega,by omega,hcredit⟩

theorem two_component_zero_energy_unpaid_parameters (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0) :
    sourceHalfPeak p=2 ∧ n-p.support.card=n%2 := by
  have hnot := two_component_zero_energy_not_unit_peak hn p hmaj hc root hlarge he
  have h := unpaid_two_component_activity (by omega) p hmaj hmax hc hpos
  dsimp only at h
  rw [he] at h
  have hp : n%2 ≤ 1 := by omega
  omega

theorem two_component_unit_energy_unpaid_parameters (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card ≤ 2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1) :
    n%4=2 ∧ ((n-p.support.card=1 ∧ sourceHalfPeak p=1) ∨ n-p.support.card=2) ∧
      sourceHalfPeak p ≤ 4 := by
  have hn4 := unit_energy_reserve_size_mod_four p he
  have h := unpaid_two_component_activity hn p hmaj hmax hc hpos
  dsimp only at h
  rw [he] at h
  have hp : n%2=0 := by omega
  rw [hp] at h
  omega

/-- Full routing reduction to explicit zero- and unit-energy regimes. These
are necessary remaining cases, not a claim that any of them are unpaid. -/
theorem two_component_sharp_or_low_energy_cases (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      ((eps=0 ∧ sourceHalfPeak p=2 ∧ n-p.support.card=n%2) ∨
        (eps=1 ∧ n%4=2 ∧ ((n-p.support.card=1 ∧ sourceHalfPeak p=1) ∨ n-p.support.card=2) ∧
          sourceHalfPeak p ≤ 4))) := by
  dsimp only
  rcases two_component_sharp_or_unit_energy_peak hn p hmaj hmax hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · obtain ⟨hne,hboth,hpos,hf,he,hU⟩ := hp
    have hmass := majorized_canonical_energy p hmaj
    have hcases : (((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0) ∨
      (((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1) := by omega
    refine Or.inr ⟨hne,hboth,hpos,?_⟩
    rcases hcases with he0 | he1
    · exact Or.inl ⟨he0,two_component_zero_energy_unpaid_parameters hn p hmaj hmax hc root hlarge hpos he0⟩
    · exact Or.inr ⟨he1,two_component_unit_energy_unpaid_parameters (by omega) p hmaj hmax hc hpos hf he1⟩

#print axioms unit_energy_reserve_size_mod_four
#print axioms two_component_zero_energy_unpaid_parameters
#print axioms two_component_unit_energy_unpaid_parameters
#print axioms two_component_sharp_or_low_energy_cases
end LRX.FiniteCuts
