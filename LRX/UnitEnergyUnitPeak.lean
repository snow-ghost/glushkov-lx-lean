import LRX.FixedCorrectedDensity

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The fixed-position correction excludes epsilon=1 and a unit source peak. -/
theorem unit_energy_unit_peak_scalar_impossible (m a f v r S2 : ℤ)
    (ha : 0 ≤ a) (hf : 1 ≤ f) (hv : 2 ≤ v)
    (hm : v+a+1 ≤ m) (hr : a+4 ≤ r) (hV : 2 ≤ 2*m-r)
    (hcap : S2 ≤ (m-1)*(2*m-r))
    (henv : S2 ≤ (m-1)^2+(m+1-r)^2)
    (hden : 2*(m^2-1)+f ≤ 4*(2*m-v-a-1)+S2+a) : False := by
  have hm3 : 3 ≤ m := by omega
  have hr4 : 4 ≤ r := by omega
  have hr5 : r ≤ 5 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-6 by omega)
    nlinarith only [hprod,hcap,hden,ha,hf,hv,hm3]
  interval_cases r <;> nlinarith only [henv,hden,ha,hf,hv,hV]

/-- All numerical premises above follow from the actual selected windows. -/
theorem actual_unit_energy_unit_peak_impossible (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : (nontrivialSuffixComponents p (componentSet p 0).card).card=1)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1)
    (hf : 1 ≤ n-p.support.card) (hU : sourceHalfPeak p=1) : False := by
  let L := (componentSet p 0).card
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let a := (singletonSuffixComponents p L).card
  let m : ℤ := (n/2 : ℕ)
  let r : ℤ := (prefixSourceCore p).card+(a : ℤ)
  let S2 := ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
  have hp4 := unit_energy_reserve_size_mod_four p he
  have hp : n%2=0 := by omega
  have hn : (n : ℤ)=2*m := by dsimp only [m]; omega
  have hc : 2 ≤ L := by have := NeZero.pos n; dsimp only [L]; omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  change v+a=n-L at htail
  have hLn : L < n := hproper
  have hLlarge : (n+1)/2 < L := hlarge
  have hm : (v : ℤ)+(a : ℤ)+1 ≤ m := by dsimp only [m]; omega
  have hLi : (L : ℤ)=2*m-v-a := by omega
  have hg := actual_two_component_peak_geometry p hmaj hlarge hproper ht
  dsimp only at hg
  rw [hp] at hg
  obtain ⟨hv,hr,hcap,henv,_,_⟩ := hg
  have hsize := area_core_size_partition p hc hproper
  have hlow := area_window_total_size_lower p L
  rw [ht] at hlow
  have hV : 2 ≤ 2*m-r := by dsimp only [r,a,L] at *; omega
  have hden := prefix_component_fixed_density_bound p hlarge hproper
  dsimp only at hden
  rw [hU] at hden
  have hmass : (∑ i, |displacement p.symm i|)=m^2-1 := by
    change m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)=1 at he
    rw [hn] at he
    nlinarith only [he]
  rw [hmass] at hden
  apply unit_energy_unit_peak_scalar_impossible m a ((n-p.support.card : ℕ) : ℤ) v r S2
    (Int.natCast_nonneg _) (by exact_mod_cast hf) hv hm hr hV
  · simpa only [Nat.cast_zero,add_zero] using hcap
  · simpa only [Nat.cast_zero,add_zero] using henv
  · change 2*(m^2-1)+((n-p.support.card : ℕ) : ℤ) ≤
      4*(1 : ℕ)*((L : ℤ)-(1 : ℕ))+S2+(a : ℤ) at hden
    rw [hLi] at hden
    simpa only [Nat.cast_one,mul_one] using hden

/-- Unit energy reserve excludes a unit source peak in the original map,
not merely in the normalization used by the window argument. -/
theorem two_component_unit_energy_not_unit_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1) (hf : 1 ≤ n-p.support.card) :
    sourceHalfPeak p ≠ 1 := by
  intro hU
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
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
  have ht : (nontrivialSuffixComponents q (componentSet q 0).card).card=1 := by rw [hzero]; omega
  apply actual_unit_energy_unit_peak_impossible q hqm hlq hpq ht
  · dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  · have hsq : q.support.card=p.support.card := by
      dsimp only [q]
      rw [local_target_zero]
      simpa only [inv_inv] using Equiv.Perm.card_support_conj
        (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
    simpa only [hsq] using hf
  · dsimp only [q]
    rw [component_cut_source_half_peak]
    exact hU

/-- The two remaining energy regimes now both have source peak at least two. -/
theorem two_component_sharp_or_nonunit_low_energy (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish ∧ 1 ≤ peakExcess p hc ∧
      ((eps=0 ∧ sourceHalfPeak p=2 ∧ n-p.support.card=n%2) ∨
        (eps=1 ∧ n%4=2 ∧ n-p.support.card=2 ∧ 2 ≤ sourceHalfPeak p ∧
          sourceHalfPeak p ≤ 4))) := by
  dsimp only
  rcases two_component_sharp_or_low_energy_cases hn p hmaj hmax hc root hlarge start finish with hw | hp
  · exact Or.inl hw
  · obtain ⟨hne,hboth,hpos,hcases⟩ := hp
    refine Or.inr ⟨hne,hboth,hpos,?_⟩
    rcases hcases with he0 | ⟨he1,hn4,hf,hU⟩
    · exact Or.inl he0
    · have hfpos : 1 ≤ n-p.support.card := by rcases hf with hh | hh <;> omega
      have hnot := two_component_unit_energy_not_unit_peak hn p hmaj hc root hlarge he1 hfpos
      have hact := unpaid_two_component_activity (by omega) p hmaj hmax hc hpos
      dsimp only at hact
      refine Or.inr ⟨he1,hn4,?_,?_,hU⟩
      · rcases hf with hh | hh <;> omega
      · omega

#print axioms unit_energy_unit_peak_scalar_impossible
#print axioms actual_unit_energy_unit_peak_impossible
#print axioms two_component_unit_energy_not_unit_peak
#print axioms two_component_sharp_or_nonunit_low_energy
end LRX.FiniteCuts
