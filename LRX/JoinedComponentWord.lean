import LRX.JoinedComponentReach

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_components_service_at (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r : Fin n)
    (hroot : p.symm r ≠ r)
    (hru : FiniteReach p r (bridgeEndpoints p hc ⟨0,hk⟩).1) :
    ∃ s : ExactService n, s.service.port=r ∧ s.service.target=joinedComponents p hc ∧
      s.displacement=displacement (joinedComponents p hc).symm ∧
      (BufferProgram.rotations s.service.word : ℤ) ≤
        (∑ i, |displacement p.symm i|)+2*(bridgeBudget (componentBridges p hc) : ℤ)-
          portLoad (displacement p.symm) r := by
  have hs := bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)
  have hm : (joinedComponents p hc).symm r ≠ r := by
    apply (mem_support_inverse (joinedComponents p hc) r).mp
    change r ∈ (bridgeSequence p (componentBridges p hc)).support
    rw [hs]
    exact (mem_support_inverse p r).mpr hroot
  have hr : ∀ i, (joinedComponents p hc).symm i ≠ i → FiniteReach (joinedComponents p hc) r i := by
    intro i hi
    exact (bridge_sequence_preserves_reach p _ (component_bridges_valid p hc)
      (component_bridges_separated p hc) hru).trans (joined_components_all_reached p hc hk i hi)
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := finite_reachable_exact_service hn _ r hm hr
  refine ⟨s,hport,htarget,hdisp,?_⟩
  have hmass := (joined_components_prices p hc).2.1
  have hl : portLoad (displacement p.symm) r ≤ portLoad (displacement (joinedComponents p hc).symm) r := by
    rw [port_load_eq_twice_half,port_load_eq_twice_half]
    have hh := bridge_sequence_half_load p _ (component_bridges_valid p hc)
      (component_bridges_separated p hc) (r.val+1)
    exact_mod_cast (show 2*halfLoad p.symm (r.val+1) ≤ 2*halfLoad (joinedComponents p hc).symm (r.val+1) from Nat.mul_le_mul_left 2 hh)
  rw [hmass] at hrot
  omega

theorem joined_components_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r start finish : Fin n)
    (hroot : p.symm r ≠ r)
    (hru : FiniteReach p r (bridgeEndpoints p hc ⟨0,hk⟩).1) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-portLoad (displacement p.symm) r+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := joined_components_service_at hn p hc hk r hroot hru
  have hcan : ∀ a ∈ [s], ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ) := by
    intro a ha i
    have he : a=s := by simpa using ha
    subst a
    rw [hdisp,htarget]
    rfl
  have hbelow : FiniteRankOrder.Below p ([s].map (fun a : ExactService n => a.service.target)).prod := by
    simpa only [List.map_singleton,List.prod_singleton,htarget] using
      (joined_components_prices p hc).1
  obtain ⟨w,he,_,_,_,hlen⟩ := arbitrary_finite_route_rank_transfer hn [s] (by simp) hcan p hbelow start finish
  have hcost : BufferProgram.rotations (route start finish ([s].map ExactService.service))=
      BufferProgram.rotations s.service.word+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val)) := by
    simp [route_rotations,walkCost,hport,Nat.add_assoc]
  rw [hcost] at hlen
  have hlen' : (w.length : ℤ)=(inversionNumber p : ℤ)+BufferProgram.rotations s.service.word+
      (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
    exact_mod_cast hlen.trans (Nat.add_assoc _ _ _).symm
  refine ⟨w,he,?_⟩
  omega

/-- An actual original-map word for any finite permutation with at least two
nontrivial load components. The estimate is not yet the sharp diameter bound. -/
theorem many_components_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (start finish : Fin n) :
    ∃ (r : Fin n) (w : List Letter),
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*((n-p.support.card+k : ℕ) : ℤ)-portLoad (displacement p.symm) r+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
  let r := (bridgeEndpoints p hc ⟨0,hk⟩).1
  have hv := ordered_component_bridge_valid p hc ⟨0,hk⟩
  have hm : p.symm r ≠ r := by
    intro he
    have hh := congrArg Fin.val he
    have hh2 : (p.symm r).val < r.val := hv.2.1
    omega
  obtain ⟨w,he,hlen⟩ := joined_components_word hn p hc hk r start finish hm Relation.ReflTransGen.refl
  have hb : (bridgeBudget (componentBridges p hc) : ℤ) ≤ ((n-p.support.card+k : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (component_bridge_budget p hc)
  exact ⟨r,w,he,by omega⟩

#print axioms joined_components_service_at
#print axioms joined_components_word
#print axioms many_components_word
end LRX.FiniteCuts
