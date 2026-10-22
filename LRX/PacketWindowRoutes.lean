import LRX.WindowFamilyBridge
import LRX.PacketRootChildrenRoutes
import LRX.WindowReachability

/-! Both window boundary routes for a multi-cycle root packet. Finite-window
closure proves that the selected children avoid the complete root core. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem packet_window_left_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (l : List (State b)) (hcycles : ∀ q ∈ l, q.IsCycle)
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (hparts : ∀ q ∈ l, CyclePart.IsPart q filling)
    (y : ℕ) (hy : y ≤ b) (hpos : ∀ q ∈ l, 0 < FiniteCuts.leftPeak q y)
    (finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-
        2*(l.map (fun q => (FiniteCuts.leftPeak q y : ℤ))).sum+(finish.val : ℤ) := by
  let targets := l.map (fun q => (permutation W q)⁻¹)
  let selected := targets.prod
  have htargets : targets.Pairwise Equiv.Perm.Disjoint :=
    List.pairwise_map.mpr (hdis.imp (fun h => (permutation_disjoint W _ _ h).inv_left.inv_right))
  have hpart : CyclePart.IsPart selected p := by
    apply CyclePart.product targets p htargets
    intro q hq
    change q ∈ l.map (fun q => (permutation W q)⁻¹) at hq
    obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
    have h := CyclePart.trans (CyclePart.window W (hparts q0 hq0)) (CyclePart.window_part W filling p.symm hmatch)
    exact CyclePart.inverse h
  have hzero : ¬Contains W (0 : Fin n) := by unfold Contains; simp; omega
  have hsupport (j : Fin n) (hj : j ∈ selected.support) : Contains W j := by
    obtain ⟨q,hq,hm⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hj
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hq
    by_contra h
    have hf : (permutation W q)⁻¹ j=j := by
      change (permutation W q).symm j=j
      rw [permutation_symm]
      exact permutation_outside W q.symm j h
    exact (Equiv.Perm.mem_support.mp hm) hf
  have hcore := selected_window_keeps_core W p selected d filling hmatch hfinite 0 hzero hsupport
  have hfin : ∀ j ∈ selected.support, d j=(selected.symm j : ℤ)-(j : ℤ) := by
    intro j hj
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp (hsupport j hj)
    rw [← CyclePart.inverse_on_support selected p hpart (embed W i) hj,hmatch,hfinite]
    simp [FiniteCuts.displacement,embed]
  obtain ⟨ss,ht,hdisp,hports,hprice⟩ := left_window_family hn W l hcycles y hy hpos
  have hc := window_family_canonical W l ss ht hdisp
  have hsdis := window_family_disjoint W l hdis ss ht
  have hprod : (ss.map (fun a => a.service.target)).prod=selected := by rw [ht]
  have hm : (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)=
      (l.map (fun q => ∑ i : Fin b, |FiniteCuts.displacement q i|)).sum := by
    have h := canonical_family_mass ss hsdis hc
    rw [hprod] at h
    exact h.symm.trans (window_family_mass W l ss hdisp)
  have hprice' : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-
        2*(l.map (fun q => (FiniteCuts.leftPeak q y : ℤ))).sum := by
    rw [hprice,sum_price,hm]
  exact packet_root_children_left_route hn hd hshort hroot hcover hpart hcore hfin ss hsdis hc hprod
    _ hprice' finish (by intro a ha; have := (hports a ha).2; omega)


theorem packet_window_right_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hr : r ≠ 0) (hroot : d r ≠ 0)
    (hcover : PrunedLift.PacketCover p d r) (W : Window n b) (hedge : W.offset+b=r.val)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (l : List (State b)) (hcycles : ∀ q ∈ l, q.IsCycle)
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (hparts : ∀ q ∈ l, CyclePart.IsPart q filling)
    (x : ℕ) (hx : x ≤ b) (hpos : ∀ q ∈ l, 0 < FiniteCuts.rightPeak q x)
    (start finish : Fin n) (hcovert : start.val+1 ≤ W.offset+x)
    (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-
        2*(l.map (fun q => (FiniteCuts.rightPeak q x : ℤ))).sum+2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  let targets := l.map (fun q => (permutation W q)⁻¹)
  let selected := targets.prod
  have htargets : targets.Pairwise Equiv.Perm.Disjoint :=
    List.pairwise_map.mpr (hdis.imp (fun h => (permutation_disjoint W _ _ h).inv_left.inv_right))
  have hpart : CyclePart.IsPart selected p := by
    apply CyclePart.product targets p htargets
    intro q hq
    change q ∈ l.map (fun q => (permutation W q)⁻¹) at hq
    obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
    have h := CyclePart.trans (CyclePart.window W (hparts q0 hq0)) (CyclePart.window_part W filling p.symm hmatch)
    exact CyclePart.inverse h
  have hsupport (j : Fin n) (hj : j ∈ selected.support) : Contains W j := by
    obtain ⟨q,hq,hm⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hj
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hq
    by_contra h
    have hf : (permutation W q)⁻¹ j=j := by
      change (permutation W q).symm j=j
      rw [permutation_symm]
      exact permutation_outside W q.symm j h
    exact (Equiv.Perm.mem_support.mp hm) hf
  have hrootoutside : ¬Contains W r := by unfold Contains; omega
  have hcore := selected_window_keeps_core W p selected d filling hmatch hfinite r hrootoutside hsupport
  have hleft (j : Fin n) (hj : j ∈ selected.support) : j.val < r.val := by
    have h := (hsupport j hj).2
    omega
  have hanchor : (r-1 : Fin n).val+1=r.val := by
    rw [Fin.val_sub_one_of_ne_zero hr]
    have := Fin.val_ne_zero_iff.mpr hr
    omega
  have hs : start.val ≤ (r-1 : Fin n).val := by omega
  have hfin : ∀ j ∈ selected.support, d j=(selected.symm j : ℤ)-(j : ℤ) := by
    intro j hj
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp (hsupport j hj)
    rw [← CyclePart.inverse_on_support selected p hpart (embed W i) hj,hmatch,hfinite]
    simp [FiniteCuts.displacement,embed]
  obtain ⟨ss,ht,hdisp,hports,hprice⟩ := right_window_family hn W l hcycles x hx hpos
  have hc := window_family_canonical W l ss ht hdisp
  have hsdis := window_family_disjoint W l hdis ss ht
  have hprod : (ss.map (fun a => a.service.target)).prod=selected := by rw [ht]
  have hm : (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)=
      (l.map (fun q => ∑ i : Fin b, |FiniteCuts.displacement q i|)).sum := by
    have h := canonical_family_mass ss hsdis hc
    rw [hprod] at h
    exact h.symm.trans (window_family_mass W l ss hdisp)
  have hprice' : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-
        2*(l.map (fun q => (FiniteCuts.rightPeak q x : ℤ))).sum := by
    rw [hprice,sum_price,hm]
  exact packet_root_children_right_route hn hd hshort r hr hroot hcover hpart hcore hfin hleft ss hsdis hc hprod
    _ hprice' start finish hs hfinish (by
      intro a ha
      have hlo := (hports a ha).1
      have hhi := (hports a ha).2
      omega)


#print axioms packet_window_left_route
#print axioms packet_window_right_route
end LRX.FiniteWindow
