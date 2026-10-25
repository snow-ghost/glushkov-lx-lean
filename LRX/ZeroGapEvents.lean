import LRX.ClosedReachableService
import LRX.ZeroGapEventTravel
import LRX.ZeroGapSorting
import Mathlib

/-! The sorting trace yields an ordered event list in the original physical
coordinates, together with factorization and noncrossing certificates. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem SortingTrace.events {p : State n} {d : Fin n → ℤ} {M : ℕ}
    (ht : SortingTrace p d M) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧ events.length=M ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧ (∀ e ∈ events, d e.1 ≠ 0 ∧ d e.2 ≠ 0) ∧
      events.Pairwise LaterOutside ∧ (∀ e ∈ events, 2*distance e.1 e.2 < n) ∧
      (∀ i, Travel events i (p.symm i) (d i)) := by
  induction ht with
  | @done p d hz =>
    have hp : p=1 := by
      apply Equiv.ext
      intro i
      have h := AffineLift.lift_residue hd (p i)
      simpa only [hz,Int.cast_zero,add_zero,p.symm_apply_apply,Equiv.Perm.one_apply] using h
    exact ⟨[],by simp [hp],rfl,by simp,by simp,List.Pairwise.nil,by simp,by intro i; simpa [hp,hz,← Equiv.Perm.inv_def] using (Travel.refl (events := []) i)⟩
  | @step p d u v hv hpos hneg hgap M ht ih =>
    have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
    have hlocal := RotationWords.recentered_lift (0 : Fin n) u (by simpa using hd)
    have hs : ∀ i, 2*|RotationWords.localDisplacement d u i| < (n : ℤ) := fun i => hshort ((L n^u.val) i)
    have hA := positive_endpoint_length hlocal v hpos hgap
    have hB := negative_endpoint_length hlocal v hneg hgap
    have hvshort : 2*v.val < n := by
      have h := hs 0
      rw [abs_of_pos hpos] at h
      omega
    obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hshortEvents,htravel⟩ := ih (exchange_lift hlocal v hv0)
      (exchange_short _ v hv0 hA hB hs)
    let base := (0,v)::events
    let result := base.map (rotateEvent u)
    have hbase_active : ∀ e ∈ base,
        RotationWords.localDisplacement d u e.1 ≠ 0 ∧ RotationWords.localDisplacement d u e.2 ≠ 0 := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact ⟨ne_of_gt hpos,ne_of_lt hneg⟩
      · have he' := hactive e he
        exact ⟨exchange_active_subset _ v e.1 hpos hneg he'.1,
          exchange_active_subset _ v e.2 hpos hneg he'.2⟩
    have hbase_neq : ∀ e ∈ base, e.1 ≠ e.2 := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact Ne.symm hv0
      · exact hneq e he
    have hbase_sep : base.Pairwise LaterOutside := List.Pairwise.cons
      (fun e he => zero_gap_excludes_active_event _ v hgap e (hbase_active e (List.mem_cons_of_mem _ he))) hsep
    have hbase_prod : (base.map eventSwap).prod=RotationWords.localTarget p 0 u := by
      simp only [base,List.map_cons,List.prod_cons,eventSwap,hprod,← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hbase_travel : ∀ i, Travel base i ((RotationWords.localTarget p 0 u).symm i)
        (RotationWords.localDisplacement d u i) := by
      intro i
      have ht := (htravel (Equiv.swap 0 v i)).mono
        (fun e he => List.mem_cons_of_mem (0,v) he)
      have hj : (Equiv.swap 0 v * RotationWords.localTarget p 0 u).symm
          (Equiv.swap 0 v i) = (RotationWords.localTarget p 0 u).symm i := by
        change (Equiv.swap 0 v * RotationWords.localTarget p 0 u)⁻¹
          (Equiv.swap 0 v i) = (RotationWords.localTarget p 0 u)⁻¹ i
        simp [Equiv.Perm.mul_apply]
      rw [hj] at ht
      have hpath := (head_travel v i events).trans ht
      rw [exchange_motion _ v i hv0] at hpath
      exact hpath
    refine ⟨result,?_,?_,?_,?_,?_,?_,?_⟩
    · calc
        (result.map eventSwap).prod = ((base.map eventSwap).map (MulAut.conj (RotationWords.rotation u))).prod := by
          simp only [result,List.map_map,Function.comp_def,event_swap_translate]
        _ = MulAut.conj (RotationWords.rotation u) ((base.map eventSwap).prod) := (map_list_prod _ _).symm
        _ = p := by
          rw [hbase_prod,RotationWords.local_target_zero,MulAut.conj_apply]
          group
    · simp only [result,List.length_map,base,List.length_cons,hlen]
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      exact fun h => hbase_neq f hf (add_right_cancel h)
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      have h := hbase_active f hf
      simpa only [rotateEvent,RotationWords.localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using h
    · apply List.pairwise_map.mpr
      exact hbase_sep.imp (fun h => later_outside_translate u h)
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      simp only [rotateEvent,distance_translate]
      rcases List.mem_cons.mp hf with hf | hf
      · subst f
        simpa [distance] using hvshort
      · exact hshortEvents f hf

    · intro j
      have hpath := (hbase_travel (j-u)).rotate u
      have hi : j-u+u=j := sub_add_cancel j u
      have hj : (RotationWords.localTarget p 0 u).symm (j-u)+u=p.symm j := by
        rw [RotationWords.local_target_inverse]
        simp
      have hdj : RotationWords.localDisplacement d u (j-u)=d j := by
        simp [RotationWords.localDisplacement,AffineLift.rotation_power_apply]
      rw [hi,hj,hdj] at hpath
      exact hpath

theorem sorting_events {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧
      (events.length : ℤ)=(∑ i : Fin n, |d i|)-
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧ (∀ e ∈ events, d e.1 ≠ 0 ∧ d e.2 ≠ 0) ∧
      events.Pairwise LaterOutside ∧ (∀ e ∈ events, 2*distance e.1 e.2 < n) ∧
      (∀ i, Travel events i (p.symm i) (d i)) := by
  obtain ⟨M,ht,hcount⟩ := exists_sorting_trace hd hshort
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hshortEvents,htravel⟩ := ht.events hd hshort
  exact ⟨events,hprod,by rw [hlen]; omega,hneq,hactive,hsep,hshortEvents,htravel⟩

#print axioms SortingTrace.events
#print axioms sorting_events
end LRX.ZeroGap
