import LRX.ComponentDensityBound
import LRX.AreaWindowSizeBounds
import LRX.CoupledPeakCutoff

/-! The new all-size support estimate instantiated on the actual C5 windows
of an initial large component. Only epsilon's unpaid bound remains explicit;
positive peak, interval sizes, partition and density are derived. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem actual_peak_support_bound (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : 2 ≤ (nontrivialSuffixComponents p (componentSet p 0).card).card)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤
      3*((nontrivialSuffixComponents p (componentSet p 0).card).card : ℤ)+6) :
    ((prefixSourceCore p).card : ℤ)+
      ((singletonSuffixComponents p (componentSet p 0).card).card : ℤ) ≤
      8*(sourceHalfPeak p : ℤ)+1-(n%2 : ℕ) := by
  let L := (componentSet p 0).card
  let t := (nontrivialSuffixComponents p L).card
  let a := (singletonSuffixComponents p L).card
  let V := ((areaWindowFamily p L).map (fun A => A.size)).sum
  let S2 := ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
  let r : ℤ := (prefixSourceCore p).card + (a : ℤ)
  let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have hnpos := NeZero.pos n
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hU : 1 ≤ sourceHalfPeak p := by
    obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc hproper
    have hmov : (sourceTarget p).symm 0 ≠ 0 := by
      simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hzero] using
        ((mem_source_packets p 0).mp hzero).1
    exact moved_global_peak_positive (sourceTarget p).symm 0 hmov
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix, ← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  have hmass := nontrivial_suffix_size_sum p L
  have hm : 2*t+1 ≤ n/2 := by dsimp [t,L] at *; omega
  have hL : L ≤ n-2*t := by dsimp [t] at *; omega
  have hpart := area_core_size_partition p hc hproper
  have hpart' : (V : ℤ)+r=n := by
    dsimp [V,r,a,L]
    exact_mod_cast (show ((areaWindowFamily p (componentSet p 0).card).map (fun A => A.size)).sum +
      ((prefixSourceCore p).card + (singletonSuffixComponents p (componentSet p 0).card).card) = n by
        simpa only [Nat.add_assoc] using hpart)
  have hn : (n : ℤ) = 2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have hcap := area_window_square_sum_cap p hmaj hlarge hproper
  have hcap' : S2 ≤ (((n/2 : ℕ) : ℤ)-1)*
      (2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-r) := by
    replace hcap : S2 ≤ ((n/2-1 : ℕ) : ℤ)*(V : ℤ) := by
      simpa only [S2,V,L,Nat.cast_list_sum,List.map_map,Function.comp_def] using hcap
    have hcst : ((n/2-1 : ℕ) : ℤ)=((n/2 : ℕ) : ℤ)-1 := by omega
    rw [hcst] at hcap
    have hv : (V : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-r := by omega
    rwa [hv] at hcap
  have hden := prefix_component_density_bound p hlarge hproper
  change 2*(∑ i, |displacement p.symm i|) ≤
    4*(sourceHalfPeak p : ℤ)*((L : ℤ)-sourceHalfPeak p)+S2 at hden
  have harea : 2*(((n/2 : ℕ) : ℤ)*(((n/2 : ℕ) : ℤ)+(n%2 : ℕ))-eps) ≤
      4*(sourceHalfPeak p : ℤ)*(2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2*(t : ℤ)-0-sourceHalfPeak p)+S2 := by
    have hl : (L : ℤ)+2*(t : ℤ) ≤ n := by omega
    have hprod := mul_nonneg (show (0 : ℤ) ≤ sourceHalfPeak p by positivity)
      (show (0 : ℤ) ≤ (n : ℤ)-2*(t : ℤ)-(L : ℤ) by omega)
    dsimp only [eps]
    nlinarith
  have hp : ((n%2 : ℕ) : ℤ)=0 ∨ ((n%2 : ℕ) : ℤ)=1 := by omega
  exact CoupledPeakCutoff.support_cap_all_sizes ((n/2 : ℕ) : ℤ) (n%2 : ℕ)
    (t : ℤ) (sourceHalfPeak p : ℤ) eps 0 r S2
    (by exact_mod_cast ht) (by exact_mod_cast hm) hp (by exact_mod_cast hU)
    he (by omega) harea hcap'

#print axioms actual_peak_support_bound
end LRX.FiniteCuts
