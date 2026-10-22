import LRX.AreaFixedComplement
import LRX.LargeComponentInternalSharpWord

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- C9 at a genuine initial component, with exactly the singleton parameter of C7. -/
theorem prefix_component_area_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    let L := (componentSet p 0).card
    let As := areaWindowFamily p L
    let V := (As.map (fun A => A.size)).sum
    let a := (singletonSuffixComponents p L).card
    let f := n-p.support.card
    let ε := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (V : ℤ)^2-2*(As.map (fun A => (A.size : ℤ)^2)).sum+
      2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
      2*(2*ε+(n%2 : ℕ)-(f : ℤ)) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < (componentSet p 0).card ↔
      i.val < (componentSet p 0).card := by
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have h := actual_window_area_deficit p hmaj (componentSet p 0).card hproper.le hcut
  dsimp only at h ⊢
  rw [area_fixed_complement_card p hc hproper] at h
  have hs : Equiv.Perm.support p.symm = p.support := Equiv.Perm.support_inv p
  simpa only [hs] using h

/-- C9 for any selected nontrivial proper component of the original map.
The recentering, invariant cut, windows and singleton identification are derived. -/
theorem component_area_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hc : 2 ≤ (componentSet p root).card) (hproper : (componentSet p root).card < n) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let As := areaWindowFamily q L
    let V := (As.map (fun A => A.size)).sum
    let a := (singletonSuffixComponents q L).card
    let f := n-q.support.card
    let ε := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|)
    (V : ℤ)^2-2*(As.map (fun A => (A.size : ℤ)^2)).sum+
      2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
      2*(2*ε+(n%2 : ℕ)-(f : ℤ)) := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hzero : (componentSet q 0).card = (componentSet p root).card := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    have he : componentSet p root = componentSet p r :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card = (componentSet p r).card at h
    rwa [← he] at h
  have hz := component_left_port_zero p root
  have hr : componentLeft p root-1+1 = r := by dsimp [r]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 (componentLeft p root-1) hd hmaj hz
  rw [hr] at hqm
  have h := prefix_component_area_deficit q hqm (by omega) (by omega)
  dsimp only at h ⊢
  rw [hzero] at h
  exact h

#print axioms prefix_component_area_deficit
#print axioms component_area_deficit
end LRX.FiniteCuts
