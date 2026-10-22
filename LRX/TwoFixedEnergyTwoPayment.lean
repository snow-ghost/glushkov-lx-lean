import LRX.ThreeFixedPeakPayment
import LRX.TwoFixedEnergyTwoGeometry

set_option maxHeartbeats 800000
namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual f=2, epsilon=2 row is paid using balanced core capacity,
the split-window square bound and even energy. -/
theorem two_component_peak_paid_of_two_fixed_energy_two (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hf : n-p.support.card=2)
    (heps : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=2) :
    peakExcess p hc ≤ 0 := by
  classical
  by_contra hnot
  have hpos : 1 ≤ peakExcess p hc := by omega
  let B : ℤ := bridgeBudget (componentBridges p hc)
  let U : ℤ := sourceHalfPeak p
  let a := (isolatedVertices p).card
  let m : ℤ := (n/2 : ℕ)
  let eps := m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)
  let parity : ℤ := (n%2 : ℕ)
  have heq : eps=2 := heps
  have hp0 : 0 ≤ parity := Int.natCast_nonneg _
  have hp1 : parity ≤ 1 := by dsimp only [parity]; omega
  have haf : a ≤ 2 := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin,hf] using hh
  have hB2' : 2*B ≤ (a : ℤ)+2 := by
    dsimp only [B,a]
    exact_mod_cast two_component_twice_bridge_budget (by omega) p hmax hc
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
  change peakExcess p hc ≤ 2*B+1-U-(2*eps+(n%2 : ℕ)-2) at hprice
  have hB2 : B=2 := by omega
  have ha2 : 2 ≤ a := by omega
  have haeq : a=2 := by omega
  have hUp : U ≤ 2-parity := by dsimp only [parity] at hp0 hp1 ⊢; omega
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
  have haq : (singletonSuffixComponents q L).card=a := component_cut_singleton_count p root (by omega)
  have hsq : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hUq : (sourceHalfPeak q : ℤ)=U := by
    dsimp only [q,U]
    rw [component_cut_source_half_peak]
  have heq' : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|)=2 := by
    dsimp only [q]
    rw [component_cut_displacement_mass]
    exact heq
  have hreserve := large_component_numeric_reserve (by omega) p hmaj (by omega) root hlarge
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    2*(((nontrivialSuffixComponents q L).card : ℤ)-1)*((v : ℤ)-((nontrivialSuffixComponents q L).card : ℤ))+
    ((singletonSuffixComponents q L).card : ℤ)*(v : ℤ)+
    ((singletonSuffixComponents q L).card.choose 2 : ℤ) ≤ _ at hreserve
  rw [ht,haq,haeq] at hreserve
  norm_num only [Nat.cast_one,Nat.cast_ofNat,Nat.choose,sub_self,mul_zero,zero_mul,add_zero] at hreserve
  have hv : 2 ≤ v := by
    have hh := nontrivial_suffix_size_sum q L
    rw [ht] at hh
    exact hh
  have hnon : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hS := filling_half_peak_sum_nonneg p
  have hN := choose_two_half_identity n
  have hm : 2*(v : ℤ)+2+U ≤ m := by
    unfold peakExcess at hpos
    change 1 ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+2*B+
      m-U-fillingHalfPeakSum p-1-(n.choose 2 : ℤ) at hpos
    dsimp only [eps,m] at heq
    dsimp only [m] at hpos ⊢
    nlinarith only [hpos,hB2,heq,hN,hS,hnon,hreserve]
  have hn' : (n : ℤ)=2*m+parity := by dsimp only [m,parity]; omega
  have hmass : (∑ i, |displacement q.symm i|)=m*(m+parity)-2 := by
    change m*((n : ℤ)-m)-(∑ i, |displacement q.symm i|)=2 at heq'
    rw [hn'] at heq'
    nlinarith only [heq']
  have haq2 : (singletonSuffixComponents q L).card=2 := haq.trans haeq
  have hgeo := actual_two_component_peak_geometry q hqm hlq hpq (by rw [hzero]; exact ht)
  dsimp only at hgeo
  rw [hzero,haq2,hsq,hf,heq',hUq] at hgeo
  let r : ℤ := (prefixSourceCore q).card+2
  let S2 := ((areaWindowFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  change 2 ≤ (v : ℤ) ∧ 6 ≤ r ∧
    S2 ≤ (m-1)*(2*m+parity-r) ∧ S2 ≤ (m-1)^2+(m+parity+1-r)^2 ∧
    (2*m+parity-r)^2-2*S2+2*(2*m+parity-r-1)*2+2^2+parity ≤ 2*(2*2+parity-2) ∧
    2*(m*(m+parity)-2) ≤ 4*U*(2*m+parity-(v : ℤ)-2-U)+S2 at hgeo
  obtain ⟨_,hr,hcap,henv,harea,hden⟩ := hgeo
  have hcq : 2 ≤ (componentSet q 0).card := by omega
  let c : ℤ := ((prefixSourceCore q).card/2 : ℕ)
  have hcore : 2*c ≤ r-2 ∧ r-2 ≤ 2*c+1 := by dsimp only [c,r]; omega
  have hbalanced := prefix_component_support_density_bound q hqm hcq hpq
  rw [hmass,hzero,hn'] at hbalanced
  change 2*(m*(m+parity)-2) ≤ 2*c*(2*m+parity-c)+S2 at hbalanced
  have hsplit := prefix_component_split_square_cap q hcq hpq
  dsimp only at hsplit
  rw [hzero,haq2] at hsplit
  have hsplit' : S2 ≤ ((n : ℤ)-r-(v : ℤ))^2+(v : ℤ)^2 := by
    simpa only [S2,r,v,Nat.cast_sum,Nat.cast_ofNat] using hsplit
  rw [hn'] at hsplit'
  obtain ⟨z,hz⟩ := canonical_energy_twice q
  rw [hmass] at hz
  exact two_fixed_energy_two_scalar_impossible m parity v r U S2 c z
    (by dsimp only [parity]; omega) (by exact_mod_cast hv) hr hU hUp hm hcap henv
    (by nlinarith only [harea]) hden hcore hbalanced hsplit' hz

/-- For the already reduced fixed-count range, epsilon=2 forces f=2 and
is therefore paid by the actual geometric exclusion above. -/
theorem two_component_peak_paid_of_energy_two (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hf : n-p.support.card ≤ 2)
    (heps : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=2) :
    peakExcess p hc ≤ 0 := by
  classical
  by_contra hh
  have hpos : 1 ≤ peakExcess p hc := by omega
  let f := n-p.support.card
  have haf : (isolatedVertices p).card ≤ f := by
    have hsub : isolatedVertices p ⊆ p.supportᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_compl,Fintype.card_fin] using hh
  have hB := two_component_twice_bridge_budget (by omega) p hmax hc
  let u := (bridgeEndpoints p hc ⟨0,by decide⟩).1
  have hu : u ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,by decide⟩).1
  have hum : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using
      ((mem_source_packets p u).mp hu).1
  have hU : 1 ≤ sourceHalfPeak p := moved_global_peak_positive (sourceTarget p).symm u hum
  have hprice := peak_activity_bound (by omega) p hmaj hc (by omega)
  dsimp only at hprice
  rw [heps] at hprice
  have hf2 : n-p.support.card=2 := by change f ≤ 2 at hf; change f=2; omega
  have hpay := two_component_peak_paid_of_two_fixed_energy_two hn p hmaj hmax hc root hlarge hf2 heps
  omega

/-- Complete t=1 routing reduction with only the unit-energy peak remaining. -/
theorem two_component_sharp_or_unit_energy_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      n-p.support.card ≤ 2 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 1 ∧
      sourceHalfPeak p ≤ 4) := by
  rcases two_component_sharp_or_two_fixed_peak hn p hmaj hmax hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · obtain ⟨hne,hboth,hpos,hf,he,hU⟩ := hp
    by_cases he1 : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 1
    · exact Or.inr ⟨hne,hboth,hpos,hf,he1,hU⟩
    · have he2 : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=2 := by omega
      have hpay := two_component_peak_paid_of_energy_two hn p hmaj hmax hc root hlarge hf he2
      omega

#print axioms two_component_peak_paid_of_two_fixed_energy_two
#print axioms two_component_peak_paid_of_energy_two
#print axioms two_component_sharp_or_unit_energy_peak
end LRX.FiniteCuts
