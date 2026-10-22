import LRX.TwoComponentLowEnergyCases

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual fixed positions split into selected-window positions and
external isolated vertices: no correction term is discarded. -/
theorem area_selected_fixed_partition (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ((familyPositions (areaWindowFamily p (componentSet p 0).card) \
      Equiv.Perm.support p.symm).card)+
      (singletonSuffixComponents p (componentSet p 0).card).card = n-p.support.card := by
  classical
  let A := familyPositions (areaWindowFamily p (componentSet p 0).card)
  let S := Equiv.Perm.support p.symm
  have h := Finset.card_sdiff_add_card_inter Sᶜ A
  have hleft : Sᶜ\A=(A∪S)ᶜ := by ext i; simp; tauto
  have hright : Sᶜ∩A=A\S := by ext i; simp; tauto
  have ha := area_fixed_complement_card p hc hproper
  change (A∪S)ᶜ.card=(singletonSuffixComponents p (componentSet p 0).card).card at ha
  have hs : Equiv.Perm.support p.symm = p.support := Equiv.Perm.support_inv p
  have htotal : Sᶜ.card=n-p.support.card := by
    simp only [S,Finset.card_compl,Fintype.card_fin,hs]
  rw [hleft,hright,ha,htotal] at h
  change (A\S).card + (singletonSuffixComponents p (componentSet p 0).card).card = n-p.support.card
  omega

/-- C10 strengthened by the exact number f-a of fixed positions in the
same actual area-window family. -/
theorem prefix_component_fixed_density_bound (p : State n)
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    let L := (componentSet p 0).card
    let U := sourceHalfPeak p
    let As := areaWindowFamily p L
    2*(∑ i, |displacement p.symm i|)+((n-p.support.card : ℕ) : ℤ) ≤
      4*(U : ℤ)*((L : ℤ)-U)+(As.map (fun A => (A.size : ℤ)^2)).sum+
        ((singletonSuffixComponents p L).card : ℤ) := by
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have hwidth := large_component_source_peak_capacity p 0 hlarge
  have hcore := prefix_core_energy_bound p hwidth
  obtain ⟨hm,ha⟩ := area_window_family_spec p L hproper.le hcut
  have henergy := (window_family_selected_energy (areaWindowFamily p L) p.symm hm ha).2.2
  have hsplit := area_core_energy_partition p hc hproper
  have hfixed := congrArg (fun x : ℕ => (x : ℤ)) (area_selected_fixed_partition p hc hproper)
  simp only [Nat.cast_add] at hfixed
  change (∑ i, |displacement p.symm i|) =
    (∑ i ∈ familyPositions (areaWindowFamily p L), |displacement p.symm i|)+
      (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) at hsplit
  change (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤
    2*(sourceHalfPeak p : ℤ)*((L : ℤ)-sourceHalfPeak p) at hcore
  change 2*(∑ i, |displacement p.symm i|)+((n-p.support.card : ℕ) : ℤ) ≤
    4*(sourceHalfPeak p : ℤ)*((L : ℤ)-sourceHalfPeak p)+
      ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum+
      ((singletonSuffixComponents p L).card : ℤ)
  change ((familyPositions (areaWindowFamily p L) \ Equiv.Perm.support p.symm).card : ℤ)+
    ((singletonSuffixComponents p L).card : ℤ)=((n-p.support.card : ℕ) : ℤ) at hfixed
  nlinarith only [hcore,henergy,hsplit,hfixed]

#print axioms area_selected_fixed_partition
#print axioms prefix_component_fixed_density_bound
end LRX.FiniteCuts
