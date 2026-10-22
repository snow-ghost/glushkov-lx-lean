import LRX.FourFixedPeakGeometry
import LRX.TwoComponentTightPeakBounds

set_option maxHeartbeats 800000

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The f=4 peak is paid for the actual large two-component map. Its extreme
parameters and the m lower bound are derived from activity, C7 and the price. -/
theorem two_component_peak_paid_of_four_fixed (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hf : n-p.support.card=4) : peakExcess p hc ≤ 0 := by
  classical
  by_contra hnot
  have hpos : 1 ≤ peakExcess p hc := by omega
  let B : ℤ := bridgeBudget (componentBridges p hc)
  let U : ℤ := sourceHalfPeak p
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have hbds := two_component_unpaid_peak_tight_bounds (by omega) p hmaj hmax hc hpos
  have he4 : eps ≤ 4 := hbds.2.1
  have hact := canonical_fixed_activity_square p hmaj
  rw [hf] at hact
  change (4 : ℤ)^2 ≤ 4*eps+(n%2 : ℕ) at hact
  have hp1 : ((n%2 : ℕ) : ℤ) ≤ 1 := by omega
  have hp0 : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have heq : eps=4 := by omega
  have haf : (isolatedVertices p).card ≤ 4 := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin,hf] using hh
  have hB2 := two_component_twice_bridge_budget (by omega) p hmax hc
  have hB2' : 2*B ≤ ((isolatedVertices p).card : ℤ)+2 := by dsimp only [B]; exact_mod_cast hB2
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ U := by
    have hh := moved_global_peak_positive (sourceTarget p).symm u hum
    change 1 ≤ (leftPeak (sourceTarget p).symm n : ℤ)
    omega
  have hprice := peak_activity_bound (by omega) p hmaj hc (by omega)
  dsimp only at hprice
  rw [hf] at hprice
  change peakExcess p hc ≤ 2*B+1-U-(2*eps+(n%2 : ℕ)-4) at hprice
  have hB3 : B=3 := by omega
  have ha4 : (isolatedVertices p).card=4 := by omega
  have hUp : U ≤ 2-(n%2 : ℕ) := by omega
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
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
  have hlq : (n+1)/2 < (componentSet q 0).card := by omega
  have hproper := component_card_lt_of_multiple_roots p (by omega) root
  have hpq : (componentSet q 0).card < n := by omega
  have hcount := component_cut_external_count p root (by omega)
  change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
  have ht : (nontrivialSuffixComponents q L).card=1 := by omega
  have ha : (singletonSuffixComponents q L).card=4 :=
    (component_cut_singleton_count p root (by omega)).trans ha4
  have hsq : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hUq : (sourceHalfPeak q : ℤ)=U := by
    dsimp only [q,U]
    rw [component_cut_source_half_peak]
  have heq' : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|)=4 := by
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact heq
  have hreserve := large_component_numeric_reserve (by omega) p hmaj (by omega) root hlarge
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    2*(((nontrivialSuffixComponents q L).card : ℤ)-1)*((v : ℤ)-((nontrivialSuffixComponents q L).card : ℤ))+
    ((singletonSuffixComponents q L).card : ℤ)*(v : ℤ)+
    ((singletonSuffixComponents q L).card.choose 2 : ℤ) ≤ _ at hreserve
  rw [ht,ha] at hreserve
  norm_num only [Nat.cast_one,Nat.cast_ofNat,Nat.choose,sub_self,mul_zero,zero_mul,add_zero] at hreserve
  have hnon : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hS := filling_half_peak_sum_nonneg p
  have hN := choose_two_half_identity n
  have hm : 4*(v : ℤ)+7+U ≤ ((n/2 : ℕ) : ℤ) := by
    unfold peakExcess at hpos
    change 1 ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+2*B+
      ((n/2 : ℕ) : ℤ)-U-fillingHalfPeakSum p-1-(n.choose 2 : ℤ) at hpos
    dsimp only [eps] at heq
    nlinarith only [hpos,hB3,heq,hN,hS,hnon,hreserve]
  apply actual_four_fixed_peak_impossible q hqm hlq hpq
  · rw [hzero]; exact ht
  · rw [hsq]; exact hf
  · rw [hzero]; exact ha
  · exact heq'
  · rw [hUq]; exact hUp
  · rw [hzero,hUq]
    exact hm

#print axioms two_component_peak_paid_of_four_fixed
end LRX.FiniteCuts
