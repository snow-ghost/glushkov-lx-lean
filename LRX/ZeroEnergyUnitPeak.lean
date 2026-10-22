import LRX.TwoFixedEnergyTwoPayment

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- A unit source peak cannot attain maximal majorized energy in the large
two-component geometry. Only the common size and density bounds are used. -/
theorem zero_energy_unit_peak_scalar_impossible (m parity a v r S2 : ℤ)
    (hp : parity=0 ∨ parity=1) (ha : 0 ≤ a) (hv : 2 ≤ v)
    (hm : v+a+1 ≤ m) (hr : a+4 ≤ r)
    (hcap : S2 ≤ (m-1)*(2*m+parity-r))
    (henv : S2 ≤ (m-1)^2+(m+parity+1-r)^2)
    (hden : 2*(m*(m+parity)) ≤ 4*(2*m+parity-v-a-1)+S2) : False := by
  have hm3 : 3 ≤ m := by omega
  have hr4 : 4 ≤ r := by omega
  have hr5 : r ≤ 5 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-6 by omega)
    rcases hp with hp | hp <;> subst parity <;> nlinarith only [hprod,hcap,hden,ha,hv,hr4,hm3]
  rcases hp with hp | hp <;> subst parity <;> interval_cases r <;>
    nlinarith only [henv,hden,hm,ha,hv]

/-- Actual initial-component specialization: no energy or window certificate
is supplied besides epsilon=0 and U=1 themselves. -/
theorem actual_zero_energy_unit_peak_impossible (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : (nontrivialSuffixComponents p (componentSet p 0).card).card=1)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0)
    (hU : sourceHalfPeak p=1) : False := by
  let L := (componentSet p 0).card
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let a := (singletonSuffixComponents p L).card
  let m : ℤ := (n/2 : ℕ)
  let parity : ℤ := (n%2 : ℕ)
  let r : ℤ := (prefixSourceCore p).card+(a : ℤ)
  let S2 := ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have htail := suffix_component_parameter_sum p L hproper.le hcut
  change v+a=n-L at htail
  have hL : (n+1)/2 < L := hlarge
  have hLn : L < n := hproper
  have hm : (v : ℤ)+(a : ℤ)+1 ≤ m := by dsimp only [m]; omega
  have hg := actual_two_component_peak_geometry p hmaj hlarge hproper ht
  dsimp only at hg
  rw [he,hU] at hg
  obtain ⟨hv,hr,hcap,henv,_,hden⟩ := hg
  apply zero_energy_unit_peak_scalar_impossible m parity a v r S2
    (by dsimp only [parity]; omega) (Int.natCast_nonneg _) hv hm hr hcap henv
  simpa only [Nat.cast_one,mul_one,sub_zero] using hden

/-- Zero energy reserve excludes a unit source peak in the original map,
not merely in the normalization used by the window argument. -/
theorem two_component_zero_energy_not_unit_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0) :
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
  apply actual_zero_energy_unit_peak_impossible q hqm hlq hpq ht
  · dsimp only [q]
    rw [component_cut_displacement_mass]
    exact he
  · dsimp only [q]
    rw [component_cut_source_half_peak]
    exact hU

#print axioms zero_energy_unit_peak_scalar_impossible
#print axioms actual_zero_energy_unit_peak_impossible
#print axioms two_component_zero_energy_not_unit_peak
end LRX.FiniteCuts
