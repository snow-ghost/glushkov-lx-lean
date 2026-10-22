import LRX.TwoComponentOuterReduction

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Six actual fixed positions pay the entire first-C8 peak budget for two
components at a maximal cut. No assumption on the source-packet defect. -/
theorem two_component_peak_paid_of_six_fixed (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hf : 6 ≤ n-p.support.card) : peakExcess p hc ≤ 0 := by
  classical
  let f := n-p.support.card
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have hactivity := canonical_fixed_activity_square p hmaj
  change (f : ℤ)^2 ≤ 4*eps+(n%2 : ℕ) at hactivity
  have hf' : (6 : ℤ) ≤ f := by exact_mod_cast hf
  have hprod := mul_nonneg (show (0 : ℤ) ≤ f by positivity)
    (show (0 : ℤ) ≤ (f : ℤ)-6 by omega)
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have hA : 2*(f : ℤ) ≤ 2*eps+(n%2 : ℕ)-(f : ℤ) := by nlinarith
  have haf : (isolatedVertices p).card ≤ f := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB : bridgeBudget (componentBridges p hc) ≤ f := by
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
  have hB' : (bridgeBudget (componentBridges p hc) : ℤ) ≤ (f : ℤ) := by exact_mod_cast hB
  omega

/-- The complete two-component large branch is sharp when at least six
positions are fixed. All cursor cases, including the exterior exception,
are discharged; the remaining branch consequently has at most five. -/
theorem two_component_sharp_word_of_six_fixed (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hf : 6 ≤ n-p.support.card) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases two_component_sharp_or_peak_or_unit_reserve hn p hmaj hmax hc root hlarge start finish with hw | hp | he
  · exact hw
  · exact joined_peak_word_of_nonpositive_excess (by omega) p hc (by omega) start finish hp.1 hp.2
      (two_component_peak_paid_of_six_fixed (by omega) p hmaj hmax hc hf)
  · have hactivity := canonical_fixed_activity_square p hmaj
    rw [he.2.2.2] at hactivity
    have hf' : (6 : ℤ) ≤ ((n-p.support.card : ℕ) : ℤ) := by exact_mod_cast hf
    have hp : ((n%2 : ℕ) : ℤ) ≤ 1 := by omega
    nlinarith

/-- Exact remaining two-component cases after the proved gap and activity payments. -/
theorem two_component_sharp_or_reduced_cases (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (n-p.support.card ≤ 5 ∧
      ((start ≠ finish ∧ JoinedPositiveArcs p hc start finish) ∨
        (OuterCursorPair p hc start finish ∧ (isolatedVertices p).card=0 ∧
          ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)=1 ∧
          ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0))) := by
  by_cases hf : 6 ≤ n-p.support.card
  · exact Or.inl (two_component_sharp_word_of_six_fixed hn p hmaj hmax hc root hlarge hf start finish)
  · rcases two_component_sharp_or_peak_or_unit_reserve hn p hmaj hmax hc root hlarge start finish with hw | hr
    · exact Or.inl hw
    · exact Or.inr ⟨by omega,hr⟩

#print axioms two_component_peak_paid_of_six_fixed
#print axioms two_component_sharp_word_of_six_fixed
#print axioms two_component_sharp_or_reduced_cases
end LRX.FiniteCuts
