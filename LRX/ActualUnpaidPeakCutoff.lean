import LRX.ActualCutoffEnvelope
import LRX.CanonicalActivityDeficit

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- All geometric hypotheses of the scalar cutoff are derived from one actual
initial large component. Only the bridge budget and the two C8 inequalities
are inputs; no window family or size/density certificate is supplied. -/
theorem actual_unpaid_peak_cutoff (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : 2 ≤ (nontrivialSuffixComponents p (componentSet p 0).card).card)
    (B : ℤ)
    (hBzero : (singletonSuffixComponents p (componentSet p 0).card).card=0 →
      B ≤ ((nontrivialSuffixComponents p (componentSet p 0).card).card : ℤ))
    (hBpos : 1 ≤ (singletonSuffixComponents p (componentSet p 0).card).card →
      B ≤ ((singletonSuffixComponents p (componentSet p 0).card).card : ℤ)+
        ((nontrivialSuffixComponents p (componentSet p 0).card).card : ℤ)-1)
    (hpeak : let t : ℤ := (nontrivialSuffixComponents p (componentSet p 0).card).card
      let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
      1 ≤ 2*B+t-(sourceHalfPeak p : ℤ)-(2*eps+(n%2 : ℕ)-((n-p.support.card : ℕ) : ℤ)))
    (hreserve : let t : ℤ := (nontrivialSuffixComponents p (componentSet p 0).card).card
      let v : ℤ := ∑ C ∈ nontrivialSuffixComponents p (componentSet p 0).card, (C.card : ℤ)
      let a : ℤ := (singletonSuffixComponents p (componentSet p 0).card).card
      let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
      1 ≤ 2*B+((n/2 : ℕ) : ℤ)-(sourceHalfPeak p : ℤ)-2-2*(t-1)*(v-t)-a*v-eps) :
    (nontrivialSuffixComponents p (componentSet p 0).card).card ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577 := by
  classical
  let L := (componentSet p 0).card
  let t := (nontrivialSuffixComponents p L).card
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let a := (singletonSuffixComponents p L).card
  let f := n-p.support.card
  let m : ℤ := (n/2 : ℕ)
  let parity : ℤ := (n%2 : ℕ)
  let eps := m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)
  let U : ℤ := sourceHalfPeak p
  let As := areaWindowFamily p L
  let V := (As.map (fun A => A.size)).sum
  let S2 := (As.map (fun A => (A.size : ℤ)^2)).sum
  let r : ℤ := (prefixSourceCore p).card+(a : ℤ)
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hU : 1 ≤ U := by
    obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc hproper
    have hmov : (sourceTarget p).symm 0 ≠ 0 := by
      simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hzero] using
        ((mem_source_packets p 0).mp hzero).1
    have hh := moved_global_peak_positive (sourceTarget p).symm 0 hmov
    change 1 ≤ (leftPeak (sourceTarget p).symm n : ℤ)
    omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  have hv := nontrivial_suffix_size_sum p L
  change v+a=n-L at htail
  change 2*t ≤ v at hv
  have hm : 2*t+1 ≤ n/2 := by dsimp [L,t] at *; omega
  have hn : (n : ℤ)=2*m+parity := by dsimp [m,parity]; omega
  have haf : a ≤ f := by
    have hs : Equiv.Perm.support p.symm=p.support := Equiv.Perm.support_inv p
    have he := area_fixed_complement_card p hc hproper
    rw [hs] at he
    have hh := Finset.card_le_card (show
      (familyPositions (areaWindowFamily p L) ∪ p.support)ᶜ ⊆ p.supportᶜ from
      Finset.compl_subset_compl.mpr Finset.subset_union_right)
    rw [he] at hh
    simpa only [Finset.card_compl,Finset.card_univ,Fintype.card_fin] using hh
  have hact := canonical_fixed_activity_square p hmaj
  have hcredit := canonical_activity_credit_nonneg p hmaj
  have hshort := component_short_arrow_energy_deficit p hmaj L ht
  change (f : ℤ)^2 ≤ 4*eps+parity at hact
  change 0 ≤ 2*eps+parity-(f : ℤ) at hcredit
  change 2*(f : ℤ)+(t : ℤ)^2-2*((v : ℤ)-(t : ℤ)) ≤ eps at hshort
  change 1 ≤ 2*B+(t : ℤ)-U-(2*eps+parity-(f : ℤ)) at hpeak
  have hreserve' : 1 ≤ 2*B+m-U-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
      (a : ℤ)*(v : ℤ)-eps := by
    simpa only [v,L,t,a,m,U,eps,Nat.cast_sum] using hreserve
  have hB0 : (a : ℤ)=0 → B ≤ (t : ℤ) := fun h => hBzero (by exact_mod_cast h)
  have hB1 : 1 ≤ (a : ℤ) → B ≤ (a : ℤ)+(t : ℤ)-1 := fun h => hBpos (by exact_mod_cast h)
  have pre := CoupledPeakCutoff.unpaid_prebounds m parity t f a v B U eps
    (by exact_mod_cast ht) (by dsimp [parity]; omega) (by dsimp [parity]; omega)
    (by positivity) (by positivity) (by exact_mod_cast haf) (by exact_mod_cast hv)
    hU hB0 hB1 hact hcredit hpeak hreserve' hshort
  have henv := actual_cutoff_window_envelope p hmaj hlarge hproper ht pre.1 pre.2.1
  have hpart := area_core_size_partition p hc hproper
  have hVr : (V : ℤ)+r=n := by
    dsimp [V,r,a,As,L]
    exact_mod_cast (show (areaWindowFamily p (componentSet p 0).card |>.map (fun A => A.size)).sum +
      ((prefixSourceCore p).card+(singletonSuffixComponents p (componentSet p 0).card).card)=n by
      simpa only [Nat.add_assoc] using hpart)
  have hV : (V : ℤ)=2*m+parity-r := by omega
  have hcore := large_prefix_source_core_card p hmaj hlarge hproper
  have hlower := area_window_total_size_lower p L
  change 2*t ≤ V at hlower
  have hC9 := prefix_component_area_deficit p hmaj hc hproper
  change (V : ℤ)^2-2*S2+2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+parity ≤
    2*(2*eps+parity-(f : ℤ)) at hC9
  rw [hV] at hC9
  have hC10 := prefix_component_density_bound p hlarge hproper
  change 2*(∑ i, |displacement p.symm i|) ≤ 4*U*((L : ℤ)-U)+S2 at hC10
  have hL : (L : ℤ)=2*m+parity-(v : ℤ)-(a : ℤ) := by omega
  have hC10' : 2*(m*(m+parity)-eps) ≤
      4*U*(2*m+parity-(v : ℤ)-(a : ℤ)-U)+S2 := by
    rw [← hL]
    dsimp only [eps]
    rw [hn]
    nlinarith
  have hcap := area_window_square_sum_cap p hmaj hlarge hproper
  replace hcap : S2 ≤ ((n/2-1 : ℕ) : ℤ)*(V : ℤ) := by
    simpa only [S2,V,As,L,Nat.cast_list_sum,List.map_map,Function.comp_def] using hcap
  have hcast : ((n/2-1 : ℕ) : ℤ)=m-1 := by dsimp [m]; omega
  rw [hcast,hV] at hcap
  have result := CoupledPeakCutoff.cutoff_of_unpaid_peak m parity t f a v B U eps r S2
    (by exact_mod_cast ht) (by dsimp only [m]; exact_mod_cast hm) (by dsimp [parity]; omega)
    (by positivity) (by positivity) (by exact_mod_cast haf) (by exact_mod_cast hv)
    hU hB0 hB1 hact hcredit hpeak hreserve' hshort
    (by dsimp [r]; omega) (by
      rw [← hV]
      have ht' : 2 ≤ t := ht
      exact_mod_cast (show 3 ≤ V by omega)) hC9 hC10' hcap henv
  change t ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577
  dsimp only [m] at result
  omega

#print axioms actual_unpaid_peak_cutoff
end LRX.FiniteCuts
