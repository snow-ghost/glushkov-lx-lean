import LRX.ThreeFixedPeakGeometry
import LRX.ActualTwoComponentPeakGeometry

set_option maxHeartbeats 800000
namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Three fixed positions cannot leave the actual two-component peak unpaid:
its forced odd-parity row contradicts the common window constraints. -/
theorem two_component_peak_paid_of_three_fixed (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hf : n-p.support.card=3) : peakExcess p hc ≤ 0 := by
  classical
  by_contra hnot
  have hpos : 1 ≤ peakExcess p hc := by omega
  let B : ℤ := bridgeBudget (componentBridges p hc)
  let U : ℤ := sourceHalfPeak p
  let a := (isolatedVertices p).card
  let m : ℤ := (n/2 : ℕ)
  let eps := m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)
  have hbds := two_component_unpaid_peak_reduced_bounds hn p hmaj hmax hc root hlarge hpos
  have he2 : eps ≤ 2 := hbds.2.1
  have hact := canonical_fixed_activity_square p hmaj
  rw [hf] at hact
  change (3 : ℤ)^2 ≤ 4*eps+(n%2 : ℕ) at hact
  have hp1 : ((n%2 : ℕ) : ℤ) ≤ 1 := by omega
  have hp0 : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have heq : eps=2 := by omega
  have hparity : n%2=1 := by omega
  have haf : a ≤ 3 := by
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
  change peakExcess p hc ≤ 2*B+1-U-(2*eps+(n%2 : ℕ)-3) at hprice
  have hB2 : B=2 := by omega
  have ha2 : 2 ≤ a := by omega
  have hacases : a=2 ∨ a=3 := by omega
  have hUp : U ≤ 2 := by omega
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
  rw [ht,haq] at hreserve
  norm_num only [Nat.cast_one,sub_self,mul_zero,zero_mul,add_zero] at hreserve
  have hv : 2 ≤ v := by
    have hh := nontrivial_suffix_size_sum q L
    rw [ht] at hh
    exact hh
  have hprod := mul_nonneg (show (0 : ℤ) ≤ (a : ℤ)-2 by omega)
    (Int.natCast_nonneg v)
  have hpairs : (1 : ℤ) ≤ (a.choose 2 : ℤ) := by
    rcases hacases with ha | ha <;> rw [ha] <;> norm_num
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
    nlinarith only [hpos,hB2,heq,hN,hS,hnon,hreserve,hprod,hpairs]
  have hgeo := actual_two_component_peak_geometry q hqm hlq hpq (by rw [hzero]; exact ht)
  dsimp only at hgeo
  rw [hzero,haq,hsq,hf,hparity,heq',hUq] at hgeo
  let r : ℤ := (prefixSourceCore q).card+(a : ℤ)
  let S2 := ((areaWindowFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  change 2 ≤ (v : ℤ) ∧ (a : ℤ)+4 ≤ r ∧
    S2 ≤ (m-1)*(2*m+1-r) ∧ S2 ≤ (m-1)^2+(m+1+1-r)^2 ∧
    (2*m+1-r)^2-2*S2+2*(2*m+1-r-1)*(a : ℤ)+(a : ℤ)^2+1 ≤ 4 ∧
    2*(m*(m+1)-2) ≤ 4*U*(2*m+1-(v : ℤ)-(a : ℤ)-U)+S2 at hgeo
  obtain ⟨_,hr,hcap,henv,harea,hden⟩ := hgeo
  exact three_fixed_peak_scalar_impossible m a v r U S2 (by exact_mod_cast hacases)
    (by exact_mod_cast hv) hr hU hUp hm hcap (by nlinarith only [henv])
    (by nlinarith only [harea]) hden

/-- The complete two-component cursor reduction after paying f=3 as well. -/
theorem two_component_sharp_or_two_fixed_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      n-p.support.card ≤ 2 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 2 ∧
      sourceHalfPeak p ≤ 4) := by
  rcases two_component_sharp_or_reduced_peak hn p hmaj hmax hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · obtain ⟨hne,hboth,hpos,hf,he,hU⟩ := hp
    by_cases hf3 : n-p.support.card=3
    · have hpaid := two_component_peak_paid_of_three_fixed hn p hmaj hmax hc root hlarge hf3
      omega
    · exact Or.inr ⟨hne,hboth,hpos,by omega,he,hU⟩

#print axioms two_component_peak_paid_of_three_fixed
#print axioms two_component_sharp_or_two_fixed_peak
end LRX.FiniteCuts
