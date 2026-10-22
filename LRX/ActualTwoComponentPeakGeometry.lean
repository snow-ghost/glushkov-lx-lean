import LRX.FourFixedPeakGeometry

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- All common scalar window constraints for a real large initial component
with one exterior nontrivial component. No numerical budget is assumed. -/
theorem actual_two_component_peak_geometry (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : (nontrivialSuffixComponents p (componentSet p 0).card).card=1) :
    let m : ℤ := (n/2 : ℕ)
    let parity : ℤ := (n%2 : ℕ)
    let L := (componentSet p 0).card
    let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
    let a := (singletonSuffixComponents p L).card
    let f := n-p.support.card
    let eps := m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)
    let U : ℤ := sourceHalfPeak p
    let r : ℤ := (prefixSourceCore p).card+(a : ℤ)
    let S2 := ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
    2 ≤ (v : ℤ) ∧ (a : ℤ)+4 ≤ r ∧
      S2 ≤ (m-1)*(2*m+parity-r) ∧
      S2 ≤ (m-1)^2+(m+parity+1-r)^2 ∧
      (2*m+parity-r)^2-2*S2+2*(2*m+parity-r-1)*(a : ℤ)+(a : ℤ)^2+parity ≤
        2*(2*eps+parity-(f : ℤ)) ∧
      2*(m*(m+parity)-eps) ≤ 4*U*(2*m+parity-(v : ℤ)-(a : ℤ)-U)+S2 := by
  classical
  let L := (componentSet p 0).card
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
  have hv : 2 ≤ v := by
    have hh := nontrivial_suffix_size_sum p L
    change 2*(nontrivialSuffixComponents p (componentSet p 0).card).card ≤ v at hh
    rw [ht] at hh
    exact hh
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  change v+a=n-L at htail
  have hLlarge : (n+1)/2 < L := hlarge
  have hLn : L < n := hproper
  have hm3 : 3 ≤ m := by dsimp only [m]; omega
  have hn : (n : ℤ)=2*m+parity := by dsimp only [m,parity]; omega
  have hL : (L : ℤ)=2*m+parity-(v : ℤ)-(a : ℤ) := by omega
  have hpart := area_core_size_partition p hc hproper
  have hVr : (V : ℤ)+r=n := by
    dsimp only [V,As,L,r,a]
    exact_mod_cast (show (areaWindowFamily p (componentSet p 0).card |>.map (fun A => A.size)).sum+
      ((prefixSourceCore p).card+(singletonSuffixComponents p (componentSet p 0).card).card)=n by
      simpa only [Nat.add_assoc] using hpart)
  have hV : (V : ℤ)=2*m+parity-r := by omega
  have hcore := large_prefix_source_core_card p hmaj hlarge hproper
  have hr : (a : ℤ)+4 ≤ r := by dsimp only [r]; omega
  have hcast : ((n/2-1 : ℕ) : ℤ)=m-1 := by dsimp only [m] at hm3 ⊢; omega
  have hcap := area_window_square_sum_cap p hmaj hlarge hproper
  replace hcap : S2 ≤ ((n/2-1 : ℕ) : ℤ)*(V : ℤ) := by
    simpa only [S2,V,As,L,Nat.cast_list_sum,List.map_map,Function.comp_def] using hcap
  rw [hcast,hV] at hcap
  have hentry (A : FillingWindow n) (hA : A ∈ As) : (A.size : ℤ) ≤ m-1 := by
    rw [← hcast]
    exact_mod_cast area_window_size_cap p hmaj hlarge hproper A hA
  have htotal : (As.map (fun A => (A.size : ℤ))).sum ≤ 2*(m-1) := by
    have hh := area_window_total_size_cap p hmaj hlarge hproper
    have hh' : (V : ℤ) ≤ 2*((n/2-1 : ℕ) : ℤ) := by exact_mod_cast hh
    rw [hcast] at hh'
    simpa only [V,Nat.cast_list_sum,List.map_map,Function.comp_def] using hh'
  have henv := window_two_cap_envelope As (m-1) (by omega) hentry htotal
  have hsum : (As.map (fun A => (A.size : ℤ))).sum=(V : ℤ) := by
    simp only [V,Nat.cast_list_sum,List.map_map,Function.comp_def]
  rw [hsum,hV] at henv
  have harea := prefix_component_area_deficit p hmaj hc hproper
  change (V : ℤ)^2-2*S2+2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+parity ≤
    2*(2*eps+parity-(f : ℤ)) at harea
  rw [hV] at harea
  have hden := prefix_component_density_bound p hlarge hproper
  change 2*(∑ i, |displacement p.symm i|) ≤ 4*U*((L : ℤ)-U)+S2 at hden
  have hmass : (∑ i, |displacement p.symm i|)=m*(m+parity)-eps := by
    dsimp only [eps]
    rw [hn]
    ring
  rw [hmass,hL] at hden
  change 2 ≤ (v : ℤ) ∧ (a : ℤ)+4 ≤ r ∧ _
  exact ⟨by exact_mod_cast hv,hr,hcap,by nlinarith only [henv],harea,hden⟩

#print axioms actual_two_component_peak_geometry
end LRX.FiniteCuts
