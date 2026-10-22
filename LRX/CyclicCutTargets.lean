import LRX.PhaseZeroCutWindow

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_target_recenter_twice (p : State n) (r s : Fin n) :
    localTarget (localTarget p 0 r) 0 s=localTarget p 0 (r+s) := by
  rw [local_target_zero,local_target_zero,local_target_zero,rotation_add]
  have hcomm : rotation r*rotation s=rotation s*rotation r := by
    rw [← rotation_add,← rotation_add,add_comm]
  group

theorem zero_cut_target_load (p : State n) (z t : Fin n)
    (hz : portLoad (FiniteCuts.displacement p.symm) z=0) :
    portLoad (FiniteCuts.displacement (localTarget p 0 (z+1)).symm) t=
      portLoad (FiniteCuts.displacement p.symm) (t+(z+1)) := by
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (FiniteCuts.displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using FiniteCuts.canonical_lift p.symm
  rw [← phase_zero_cut_canonical 0 z hd hz,port_load_recenter]

end LRX.RotationWords

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

noncomputable def externalWidth (p : State n) : ℕ :=
  if hp : p.support.Nonempty then n+(p.support.min' hp).val-(p.support.max' hp).val else 0

theorem external_width_eq_outer (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    externalWidth p=n+(outerLeft p hc).val-(outerRight p hc).val := by
  classical
  obtain ⟨_,hL,hR,_,_⟩ := joined_outer_ports hn p hc hk
  have hLs := (mem_support_inverse p _).mpr ((mem_source_packets p _).mp hL).1
  have hRs := (mem_support_inverse p _).mpr ((mem_source_packets p _).mp hR).1
  have hne : p.support.Nonempty := ⟨outerLeft p hc,hLs⟩
  have hmin : p.support.min' hne=outerLeft p hc := by
    apply Fin.ext
    have h1 := Finset.min'_le p.support _ hLs
    have h2 := (moving_between_outer p hc _ ((mem_support_inverse p _).mp (Finset.min'_mem p.support hne))).1
    change (p.support.min' hne).val ≤ (outerLeft p hc).val at h1
    omega
  have hmax : p.support.max' hne=outerRight p hc := by
    apply Fin.ext
    have h1 := Finset.le_max' p.support _ hRs
    have h2 := (moving_between_outer p hc _ ((mem_support_inverse p _).mp (Finset.max'_mem p.support hne))).2
    change (outerRight p hc).val ≤ (p.support.max' hne).val at h1
    omega
  simp only [externalWidth,dif_pos hne,hmin,hmax]

#print axioms external_width_eq_outer
end LRX.FiniteCuts
