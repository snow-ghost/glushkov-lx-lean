import LRX.TwoCapWindowEnvelope
import LRX.ActualCutoffEnvelope

set_option maxHeartbeats 800000

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The extreme four-fixed-point row is inconsistent with the common area,
density and two-cap bounds. No enumeration or external computation is used. -/
theorem four_fixed_peak_scalar_impossible (m parity v r U S2 : ℤ)
    (hp : parity=0 ∨ parity=1) (hv : 2 ≤ v) (hr : 8 ≤ r)
    (hU : 1 ≤ U) (hUp : U ≤ 2-parity) (hm : 4*v+7+U ≤ m)
    (hcap : S2 ≤ (m-1)*(2*m+parity-r))
    (henv : S2 ≤ (m-1)^2+(m+parity+1-r)^2)
    (harea : (2*m+parity-r)^2-2*S2+8*(2*m+parity-r-1)+16+parity ≤ 8+2*parity)
    (hdensity : 2*(m*(m+parity)-4) ≤ 4*U*(2*m+parity-v-4-U)+S2) : False := by
  have hm16 : 16 ≤ m := by omega
  have hr13 : r ≤ 13 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-14 by omega)
    rcases hp with hp | hp <;> subst parity
    · have hUcases : U=1 ∨ U=2 := by omega
      rcases hUcases with hUeq | hUeq <;> subst U <;> nlinarith
    · have hUeq : U=1 := by omega
      subst U
      nlinarith
  have hsq := mul_nonneg (show 0 ≤ 13-r by omega) (show 0 ≤ r+17 by omega)
  rcases hp with hp | hp <;> subst parity <;> nlinarith

/-- The scalar contradiction instantiated on the actual area-window family
of a large initial component. All area and density data are derived. -/
theorem actual_four_fixed_peak_impossible (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : (nontrivialSuffixComponents p (componentSet p 0).card).card=1)
    (hf : n-p.support.card=4)
    (ha : (singletonSuffixComponents p (componentSet p 0).card).card=4)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=4)
    (hUp : (sourceHalfPeak p : ℤ) ≤ 2-(n%2 : ℕ))
    (hm : 4*((∑ C ∈ nontrivialSuffixComponents p (componentSet p 0).card, C.card : ℕ) : ℤ)+
      7+(sourceHalfPeak p : ℤ) ≤ ((n/2 : ℕ) : ℤ)) : False := by
  classical
  let L := (componentSet p 0).card
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let m : ℤ := (n/2 : ℕ)
  let parity : ℤ := (n%2 : ℕ)
  let U : ℤ := sourceHalfPeak p
  let As := areaWindowFamily p L
  let V := (As.map (fun A => A.size)).sum
  let S2 := (As.map (fun A => (A.size : ℤ)^2)).sum
  let r : ℤ := (prefixSourceCore p).card+4
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hU : 1 ≤ U := by
    obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc hproper
    have hmov : (sourceTarget p).symm 0 ≠ 0 := by
      simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hzero] using
        ((mem_source_packets p 0).mp hzero).1
    have hh := moved_global_peak_positive (sourceTarget p).symm 0 hmov
    change 1 ≤ (leftPeak (sourceTarget p).symm n : ℤ)
    omega
  have hv : 2 ≤ v := by
    have hh := nontrivial_suffix_size_sum p L
    change 2*(nontrivialSuffixComponents p (componentSet p 0).card).card ≤ v at hh
    rw [ht] at hh
    exact hh
  change 4*(v : ℤ)+7+U ≤ m at hm
  have hm16 : 16 ≤ m := by omega
  have hn : (n : ℤ)=2*m+parity := by dsimp only [m,parity]; omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  change v+(singletonSuffixComponents p (componentSet p 0).card).card=n-L at htail
  rw [ha] at htail
  have hL : (L : ℤ)=2*m+parity-(v : ℤ)-4 := by omega
  have hpart := area_core_size_partition p hc hproper
  rw [ha] at hpart
  have hVr : (V : ℤ)+r=n := by
    dsimp only [V,As,L,r]
    exact_mod_cast (show (areaWindowFamily p (componentSet p 0).card |>.map (fun A => A.size)).sum+
      ((prefixSourceCore p).card+4)=n by simpa only [Nat.add_assoc] using hpart)
  have hV : (V : ℤ)=2*m+parity-r := by omega
  have hcore := large_prefix_source_core_card p hmaj hlarge hproper
  have hr : 8 ≤ r := by dsimp only [r]; omega
  have hcast : ((n/2-1 : ℕ) : ℤ)=m-1 := by dsimp only [m] at *; omega
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
  dsimp only at harea
  rw [hf,ha,he] at harea
  change (V : ℤ)^2-2*S2+2*((V : ℤ)-1)*4+4^2+parity ≤ 2*(2*4+parity-4) at harea
  rw [hV] at harea
  have hden := prefix_component_density_bound p hlarge hproper
  change 2*(∑ i, |displacement p.symm i|) ≤ 4*U*((L : ℤ)-U)+S2 at hden
  have hmass : (∑ i, |displacement p.symm i|)=m*(m+parity)-4 := by
    change m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)=4 at he
    rw [hn] at he
    nlinarith only [he]
  rw [hmass,hL] at hden
  apply four_fixed_peak_scalar_impossible m parity v r U S2
    (by dsimp only [parity]; omega) (by exact_mod_cast hv) hr hU hUp hm hcap
    (by nlinarith only [henv]) (by nlinarith only [harea]) hden

#print axioms four_fixed_peak_scalar_impossible
#print axioms actual_four_fixed_peak_impossible
end LRX.FiniteCuts
