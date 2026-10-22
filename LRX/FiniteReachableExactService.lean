import LRX.FiniteBridgeService

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem finite_reachable_exact_service (hn : 2 ≤ n) (p : State n) (r : Fin n)
    (hroot : p.symm r ≠ r) (hr : ∀ i, p.symm i ≠ i → FiniteReach p r i) :
    ∃ service : ExactService n, service.service.port=r ∧ service.service.target=p ∧
      service.displacement=displacement p.symm ∧
      (BufferProgram.rotations service.service.word : ℤ)=
        (∑ i, |displacement p.symm i|)-portLoad (displacement p.symm) r := by
  let d := displacement p.symm
  have hd : AffineLift.IsLift p 0 d := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hroot' : d r ≠ 0 := displacement_ne_of_moved p.symm r hroot
  have hreach : ∀ i, localDisplacement d r i ≠ 0 →
      PrunedLift.Reaches (localTarget p 0 r) (localDisplacement d r) 0 i := by
    intro i hi
    apply (reaches_recenter p d r (i:=0) (j:=i)).mpr
    have hz : rotation r 0=r := by simp [RotationWords.rotation,AffineLift.rotation_power_apply]
    rw [hz]
    apply hr
    intro he
    apply hi
    change displacement p.symm (rotation r i)=0
    simp only [displacement,he,sub_self]
  obtain ⟨s,hport,htarget,hx,hprice,hend⟩ := exists_exact_closed_service hn r hd
    (displacement_short p.symm) hroot' hreach
  have hstationary : ∀ i, s.target i=i → d i=0 := by
    intro i hi
    rw [htarget] at hi
    have hinv : p.symm i=i := by simpa only [Equiv.symm_apply_apply] using (congrArg p.symm hi).symm
    simp only [d,displacement,hinv,sub_self]
  let service : ExactService n := ⟨s,d,hstationary,by simpa only [hport] using hend⟩
  refine ⟨service,hport,htarget,rfl,?_⟩
  have hsplit := LiftedModel.length_eq_event_rotation s.word (LiftedModel.initial (n:=n))
  rw [LiftedModel.event_count_length] at hsplit
  have hsplit' : (s.word.length : ℤ)=(BufferProgram.exchanges s.word : ℤ)+BufferProgram.rotations s.word := by exact_mod_cast hsplit
  rw [hx] at hsplit'
  change (BufferProgram.rotations s.word : ℤ)=_
  dsimp [d] at hprice hsplit'
  omega

theorem component_bridge_service_at (hn : 2 ≤ n) (p : State n) (u v r : Fin n)
    (huv : u.val < v.val) (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (hroot : p.symm r ≠ r) (hru : FiniteReach p r u)
    (hr : ∀ i, p.symm i ≠ i → FiniteReach p u i ∨ FiniteReach p v i) :
    ∃ service : ExactService n, service.service.port=r ∧ service.service.target=componentBridge p u v ∧
      service.displacement=displacement (componentBridge p u v).symm ∧
      (BufferProgram.rotations service.service.word : ℤ) ≤
        (∑ i, |displacement p.symm i|)+2*((v : ℤ)-(u : ℤ))-portLoad (displacement p.symm) r := by
  have hroot' := component_bridge_moved p u v huv ha hb r hroot
  have hreach : ∀ i, (componentBridge p u v).symm i ≠ i → FiniteReach (componentBridge p u v) r i := by
    intro i hi
    exact (component_bridge_preserves_reach p u v huv ha hb hru).trans
      (component_bridge_all_reached p u v huv ha hb hr i
        (displacement_ne_of_moved (componentBridge p u v).symm i hi))
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := finite_reachable_exact_service hn (componentBridge p u v) r hroot' hreach
  refine ⟨s,hport,htarget,hdisp,?_⟩
  have hm := component_bridge_mass p u v huv ha hb
  have hl : portLoad (displacement p.symm) r ≤ portLoad (displacement (componentBridge p u v).symm) r := by
    rw [port_load_eq_twice_half,port_load_eq_twice_half,component_bridge_half_load p u v huv ha hb]
    split_ifs <;> push_cast <;> omega
  rw [hm] at hrot
  omega

#print axioms finite_reachable_exact_service
#print axioms component_bridge_service_at
end LRX.FiniteCuts
