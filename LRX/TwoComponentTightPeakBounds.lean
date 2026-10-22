import LRX.BridgeExteriorBudget

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Scalar consequence of the joint separator budget and first C8. -/
theorem two_component_tight_peak_arithmetic (f a B U eps parity : ℤ)
    (hf : 0 ≤ f) (haf : a ≤ f) (hB : 2*B ≤ a+2) (hU : 1 ≤ U)
    (hp0 : 0 ≤ parity) (hp1 : parity ≤ 1)
    (hactivity : f^2 ≤ 4*eps+parity) (hcredit : 0 ≤ 2*eps+parity-f)
    (hunpaid : U+(2*eps+parity-f) ≤ 2*B) :
    f ≤ 4 ∧ eps ≤ 4 ∧ U ≤ 4 := by
  have hf4 : f ≤ 4 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ f-5 by omega) (show 0 ≤ f+1 by omega)
    nlinarith
  have he4 : eps ≤ 4 := by omega
  refine ⟨hf4,he4,?_⟩
  by_contra hh
  have hB3 : 3 ≤ B := by omega
  have hfeq : f=4 := by omega
  rw [hfeq] at hactivity hunpaid
  have he : 4 ≤ eps := by omega
  omega

/-- Stronger necessary bounds for the actual unpaid t=1 peak. -/
theorem two_component_unpaid_peak_tight_bounds (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc) :
    n-p.support.card ≤ 4 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 4 ∧
      sourceHalfPeak p ≤ 4 := by
  classical
  let f := n-p.support.card
  let a := (isolatedVertices p).card
  let B : ℤ := bridgeBudget (componentBridges p hc)
  let U : ℤ := sourceHalfPeak p
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have haf : a ≤ f := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB : 2*B ≤ (a : ℤ)+2 := by
    dsimp only [B,a]
    exact_mod_cast two_component_twice_bridge_budget hn p hmax hc
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ U := by
    have hh := moved_global_peak_positive (sourceTarget p).symm u hum
    change 1 ≤ (leftPeak (sourceTarget p).symm n : ℤ)
    omega
  have hact := canonical_fixed_activity_square p hmaj
  have hcredit := canonical_activity_credit_nonneg p hmaj
  change (f : ℤ)^2 ≤ 4*eps+(n%2 : ℕ) at hact
  change 0 ≤ 2*eps+(n%2 : ℕ)-(f : ℤ) at hcredit
  have hprice := peak_activity_bound hn p hmaj hc (by omega)
  change peakExcess p hc ≤ 2*B+1-U-(2*eps+(n%2 : ℕ)-(f : ℤ)) at hprice
  have result := two_component_tight_peak_arithmetic f a B U eps (n%2 : ℕ)
    (by positivity) (by exact_mod_cast haf) hB hU (by positivity) (by omega)
    hact hcredit (by omega)
  change f ≤ 4 ∧ eps ≤ 4 ∧ sourceHalfPeak p ≤ 4
  dsimp only [U] at result
  omega

/-- The full t=1 cursor reduction with the strengthened actual peak bounds. -/
theorem two_component_sharp_or_tight_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      n-p.support.card ≤ 4 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 4 ∧
      sourceHalfPeak p ≤ 4) := by
  rcases two_component_sharp_or_peak hn p hmaj hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · by_cases hpay : peakExcess p hc ≤ 0
    · exact Or.inl (joined_peak_word_of_nonpositive_excess (by omega) p hc (by omega)
        start finish hp.1 hp.2 hpay)
    · have hpos : 1 ≤ peakExcess p hc := by omega
      exact Or.inr ⟨hp.1,hp.2,hpos,two_component_unpaid_peak_tight_bounds (by omega) p hmaj hmax hc hpos⟩

#print axioms two_component_tight_peak_arithmetic
#print axioms two_component_unpaid_peak_tight_bounds
#print axioms two_component_sharp_or_tight_peak
end LRX.FiniteCuts
