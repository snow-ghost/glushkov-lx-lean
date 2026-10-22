import LRX.InnermostEventComponent
import LRX.EventDefectParity

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- A nonempty finite permutation with full support and zero cycle defect
has a physical unit arrow, even when it has several cycles. -/
theorem full_support_zero_defect_unit_arrow (p : State n)
    (hfull : p.support=Finset.univ)
    (hzero : (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)=0) :
    ∃ i : Fin n, |displacement p i|=1 := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q := FiniteWindow.permutation W p
  obtain ⟨events,hprod,hlen,hneq,ha,hlinear,hsep⟩ := padded_sorting_events p
  have hs : q.support.card=p.support.card := FiniteWindow.permutation_support_card W p
  have hk : q.cycleFactorsFinset.card=p.cycleFactorsFinset.card := FiniteWindow.permutation_cycle_count W p
  have hki : (q⁻¹).cycleFactorsFinset.card=q.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv q)
    simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val] using hh
  have hminimal : events.length+(q⁻¹).cycleFactorsFinset.card=q.support.card := by
    rw [hki,hk,hs]
    omega
  have hcontains (j : Fin (2*n+1)) (hj : j ∈ q.support) : FiniteWindow.Contains W j := by
    by_contra hh
    exact (Equiv.Perm.mem_support.mp hj) (FiniteWindow.permutation_outside W p j hh)
  have hsupport (j : Fin (2*n+1)) : j ∈ q.support ↔ j.val < n := by
    constructor
    · intro hj
      have hh := hcontains j hj
      simpa only [W,zero_add] using hh.2
    · intro hj
      let i : Fin n := ⟨j.val,hj⟩
      have hemb : FiniteWindow.embed W i=j := Fin.ext (by simp [FiniteWindow.embed,W,i])
      rw [← hemb]
      change FiniteWindow.embed W i ∈ (FiniteWindow.permutation W p).support
      rw [FiniteWindow.permutation_support]
      exact Finset.mem_image.mpr ⟨i,by rw [hfull]; exact Finset.mem_univ _,rfl⟩
  have hint : ZeroGap.CarrierInterval q.support Finset.univ := by
    refine ⟨Finset.subset_univ _,?_⟩
    intro x hx y hy z _ _ hz
    apply (hsupport z).mpr
    have hx' := (hsupport x).mp hx
    have hy' := (hsupport y).mp hy
    omega
  have hnon : q.support.Nonempty := ⟨0,(hsupport 0).mpr (by have := NeZero.pos n; simpa)⟩
  obtain ⟨j,hj⟩ := ZeroGap.minimal_interval_event_unit_arrow events q hprod ha hlinear hsep hnon hint hminimal
  have hjin : FiniteWindow.Contains W j := by
    by_contra hh
    have hz := FiniteWindow.displacement_outside W p j hh
    change displacement q j=0 at hz
    rw [hz,abs_zero] at hj
    omega
  obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hjin
  exact ⟨i,by simpa only [q,FiniteWindow.displacement_embed] using hj⟩

/-- The needed positivity implication for arbitrary full-support permutations,
not only for one cycle. -/
theorem full_support_nonunit_defect_positive (p : State n)
    (hfull : p.support=Finset.univ) (hunit : ∀ i, |displacement p i| ≠ 1) :
    0 < (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  have hnon := finite_depth_rank p
  by_contra hh
  have hz : (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)=0 := by omega
  obtain ⟨i,hi⟩ := full_support_zero_defect_unit_arrow p hfull hz
  exact hunit i hi

/-- The exact unit lemma: a fixed-point-free permutation without unit arrows
has cycle defect at least two. -/
theorem full_support_nonunit_defect_ge_two (p : State n)
    (hfull : p.support=Finset.univ) (hunit : ∀ i, |displacement p i| ≠ 1) :
    2 ≤ (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  have hp := full_support_nonunit_defect_positive p hfull hunit
  obtain ⟨z,hz⟩ := finite_cycle_defect_even p
  omega

#print axioms full_support_zero_defect_unit_arrow
#print axioms full_support_nonunit_defect_positive
#print axioms full_support_nonunit_defect_ge_two
end LRX.FiniteCuts
