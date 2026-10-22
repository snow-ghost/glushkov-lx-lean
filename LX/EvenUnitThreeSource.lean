import LX.SingleThreeGeometry

namespace LX.CycleGeometry
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Recut at the sole fixed point and return to the original physical
circle. All three exceptional positions are cyclic neighbors. -/
theorem single_three_cyclic_consecutive (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1)
    (a : Fin n) (hfixed : ∀ i : Fin n,q i=i → i=a)
    (hback : ∀ i : Fin n,q (i+1) ≠ i) :
    ∃ u : Fin n,q u=u+1 ∧ q (u+1)=u+2 ∧ q (u+2)=u ∧
      ∀ i : Fin n,i ≠ u → i ≠ u+1 → i ≠ u+2 → q (q i)=i := by
  let Q := shiftConjugate q a.val
  have hQzero : cycleDefect Q=0 := by dsimp only [Q]; rw [shift_cycle_defect,hq]
  obtain ⟨hs,hc⟩ := shift_support_and_cycle_count q a.val
  have hQexcess : Q.support.card=2*Q.cycleFactorsFinset.card+1 := by
    change (shiftConjugate q a.val).support.card=2*(shiftConjugate q a.val).cycleFactorsFinset.card+1
    rw [hs,hc]
    exact he
  have hQfixed (i : Fin n) (hi : Q i=i) : i=0 := by
    have hh := congrArg (fun j : Fin n => j+a) hi
    simp only [Q,shift_conjugate_apply,sub_add_cancel] at hh
    have he' := hfixed (i+a) hh
    exact add_right_cancel (show i+a=0+a by simpa using he')
  have hQback (i j : Fin n) (hij : i.val+1=j.val) : Q j ≠ i := by
    intro hi
    have hj : i+1=j := LX.MatchingGeometry.eq_add_of_value_add i j 1 hij
    rw [← hj] at hi
    have hh := congrArg (fun j : Fin n => j+a) hi
    simp only [Q,shift_conjugate_apply,sub_add_cancel] at hh
    have harg : i+1+a=(i+a)+1 := by ring
    rw [harg] at hh
    exact hback (i+a) hh
  obtain ⟨u,v,w,huv,hvw,hu,hv,hw,houtside⟩ :=
    single_three_consecutive_at_zero Q hQzero hQexcess hQfixed hQback
  have hv' : v=u+1 := (LX.MatchingGeometry.eq_add_of_value_add u v 1 huv).symm
  have hw' : w=u+2 := (LX.MatchingGeometry.eq_add_of_value_add u w 2 (by omega)).symm
  have huq : q (u+a)=v+a := by
    have hh := congrArg (fun j : Fin n => j+a) hu
    simpa only [Q,shift_conjugate_apply,sub_add_cancel] using hh
  have hvq : q (v+a)=w+a := by
    have hh := congrArg (fun j : Fin n => j+a) hv
    simpa only [Q,shift_conjugate_apply,sub_add_cancel] using hh
  have hwq : q (w+a)=u+a := by
    have hh := congrArg (fun j : Fin n => j+a) hw
    simpa only [Q,shift_conjugate_apply,sub_add_cancel] using hh
  have hva : v+a=(u+a)+1 := by rw [hv']; ring
  have hwa : w+a=(u+a)+2 := by rw [hw']; ring
  rw [hva] at huq hvq
  rw [hwa] at hvq hwq
  refine ⟨u+a,huq,hvq,hwq,?_⟩
  intro i hiu hiv hiw
  have hneq (j : Fin n) (hj : i ≠ j+a) : i-a ≠ j := by
    intro he
    have hh := congrArg (fun k : Fin n => k+a) he
    exact hj (by simpa only [sub_add_cancel] using hh)
  have hh := houtside (i-a) (hneq u hiu)
    (hneq v (by rwa [hva])) (hneq w (by rwa [hwa]))
  change shiftConjugate q a.val (shiftConjugate q a.val (i-a))=i-a at hh
  rw [shift_conjugate_apply_shift,shift_conjugate_apply_shift] at hh
  have hh' := congrArg (fun j : Fin n => j+a) hh
  simpa only [sub_add_cancel] using hh'

end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- In the one-fixed-position subcase of the even unit-reserve input,
the actual exceptional cycle is a positively oriented consecutive triple.
Its position and orientation are conclusions, not routing hypotheses. -/
theorem even_unit_one_fixed_consecutive_three {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hfixed : (LRX.FiniteCuts.fixedPositions (permutation p a)).card=1) :
    ∃ u : Fin n,permutation p a u=u+1 ∧ permutation p a (u+1)=u+2 ∧
      permutation p a (u+2)=u ∧
      ∀ i : Fin n,i ≠ u → i ≠ u+1 → i ≠ u+2 → permutation p a (permutation p a i)=i := by
  obtain ⟨hz,_,_,he⟩ := even_unit_reserve_source m hn ha hunit
  rw [hfixed] at he
  have hh := (even_unit_reserve_height m hn ha hunit).1
  apply LX.CycleGeometry.single_three_cyclic_consecutive (permutation p a) hz he a
  · intro i hi
    exact Finset.card_le_one.mp hfixed.le i
      ((LRX.FiniteCuts.mem_fixedPositions _ _).mpr hi) a
      ((LRX.FiniteCuts.mem_fixedPositions _ _).mpr (permutation_anchor p a))
  · exact even_source_no_backward_unit p a (global_minimum_majorized ha) (by omega)

#print axioms even_unit_one_fixed_consecutive_three
end LX.AnchoredPhases
