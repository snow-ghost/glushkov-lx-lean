import LRX.FiniteBridgeReachability
import LRX.PacketCoordinateSymmetry

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem component_bridge_all_reached (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (hr : ∀ i, p.symm i ≠ i → FiniteReach p u i ∨ FiniteReach p v i)
    (i : Fin n) (hi : displacement (componentBridge p u v).symm i ≠ 0) :
    FiniteReach (componentBridge p u v) u i := by
  obtain ⟨hc,_⟩ := bridge_cross_edges p u v huv ha hb
  by_cases hiu : i=u
  · subst i; exact Relation.ReflTransGen.refl
  · by_cases hiv : i=v
    · subst i; exact Relation.ReflTransGen.single hc
    · have hm : p.symm i ≠ i := by
        intro he
        apply hi
        simp only [displacement,component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hiu hiv,he,sub_self]
      rcases hr i hm with hh | hh
      · exact component_bridge_preserves_reach p u v huv ha hb hh
      · exact (Relation.ReflTransGen.single hc).trans (component_bridge_preserves_reach p u v huv ha hb hh)

theorem component_bridge_service (hn : 2 ≤ n) (p : State n) (u v : Fin n)
    (huv : u.val < v.val) (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (hr : ∀ i, p.symm i ≠ i → FiniteReach p u i ∨ FiniteReach p v i) :
    ∃ service : ExactService n, service.service.port=u ∧ service.service.target=componentBridge p u v ∧
      service.displacement=displacement (componentBridge p u v).symm ∧
      (BufferProgram.rotations service.service.word : ℤ)=
        (∑ i, |displacement p.symm i|)+2*((v : ℤ)-(u : ℤ))-
          portLoad (displacement p.symm) u-2 := by
  let G := componentBridge p u v
  let d := displacement G.symm
  have hd : AffineLift.IsLift G 0 d := by
    simpa only [Equiv.symm_symm] using canonical_lift G.symm
  have hshort : ∀ i, |d i| < (n : ℤ) := displacement_short G.symm
  have hroot : d u ≠ 0 := by
    dsimp [d,G,displacement]
    rw [component_bridge_inverse,Equiv.swap_apply_left]
    have := (p.symm v).isLt
    omega
  have hreach : ∀ i, localDisplacement d u i ≠ 0 →
      PrunedLift.Reaches (localTarget G 0 u) (localDisplacement d u) 0 i := by
    intro i hi
    apply (reaches_recenter G d u (i:=0) (j:=i)).mpr
    have hzero : rotation u 0=u := by simp [RotationWords.rotation,AffineLift.rotation_power_apply]
    rw [hzero]
    exact component_bridge_all_reached p u v huv ha hb hr (rotation u i) hi
  obtain ⟨s,hport,htarget,hx,hprice,hend⟩ := exists_exact_closed_service hn u hd hshort hroot hreach
  have hstationary : ∀ i, s.target i=i → d i=0 := by
    intro i hi
    rw [htarget] at hi
    have hinv : G.symm i=i := by
      simpa only [Equiv.symm_apply_apply] using (congrArg G.symm hi).symm
    simp only [d,displacement,hinv,sub_self]
  let service : ExactService n := ⟨s,d,hstationary,by simpa only [hport] using hend⟩
  refine ⟨service,hport,htarget,rfl,?_⟩
  have hsplit := LiftedModel.length_eq_event_rotation s.word (LiftedModel.initial (n:=n))
  rw [LiftedModel.event_count_length] at hsplit
  have hsplit' : (s.word.length : ℤ)=(BufferProgram.exchanges s.word : ℤ)+BufferProgram.rotations s.word := by exact_mod_cast hsplit
  rw [hx] at hsplit'
  have hm := component_bridge_mass p u v huv ha hb
  have hl : portLoad d u=portLoad (displacement p.symm) u+2 := by
    change portLoad (displacement (componentBridge p u v).symm) u=_
    rw [port_load_eq_twice_half,port_load_eq_twice_half,component_bridge_half_load p u v huv ha hb]
    rw [if_pos (by omega : u.val < u.val+1 ∧ u.val+1 ≤ v.val)]
    push_cast
    ring
  change (BufferProgram.rotations s.word : ℤ)=_
  change (∑ i, |d i|)=(∑ i, |displacement p.symm i|)+2*((v : ℤ)-(u : ℤ)) at hm
  rw [hm,hl] at hprice
  omega

#print axioms component_bridge_all_reached
#print axioms component_bridge_service
end LRX.FiniteCuts
