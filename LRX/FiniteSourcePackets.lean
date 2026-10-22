import LRX.BridgePacketClosure

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n k : ℕ} [NeZero n]

theorem fixed_service_edge (p : State n) {i j : Fin n} (hi : p.symm i=i)
    (he : BufferProgram.ServiceEdge p (displacement p.symm) i j) : i=j := by
  rcases he with hc | ⟨hj,t,hl,hr⟩
  · exact hc.eq_of_left hi
  · simp only [displacement,hi,sub_self,add_zero,min_self,max_self] at hl hr
    have hh : (i : ℤ)=(j : ℤ)+t*(n : ℤ) := le_antisymm hl hr
    have hh' := congrArg (fun z : ℤ => (z : Fin n)) hh
    simpa using hh'

theorem fixed_service_path (p : State n) {i j : Fin n} (hi : p.symm i=i)
    (hp : FiniteReach p i j) : i=j := by
  induction hp with
  | refl => rfl
  | tail hp he ih =>
    subst ih
    exact fixed_service_edge p hi he

def SourceVertex (p : State n) (i : Fin n) : Prop :=
  p.symm i ≠ i ∧ ∀ j, FiniteReach p j i → FiniteReach p i j

noncomputable def sourcePackets (p : State n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (SourceVertex p)

@[simp] theorem mem_source_packets (p : State n) (i : Fin n) :
    i ∈ sourcePackets p ↔ SourceVertex p i := by
  classical
  simp [sourcePackets]

theorem source_packets_predecessor_closed (p : State n) (i j : Fin n)
    (he : BufferProgram.ServiceEdge p (displacement p.symm) i j)
    (hj : j ∈ sourcePackets p) : i ∈ sourcePackets p := by
  obtain ⟨hjm,hjs⟩ := (mem_source_packets p j).mp hj
  have hij : FiniteReach p i j := Relation.ReflTransGen.single he
  have hji := hjs i hij
  apply (mem_source_packets p i).mpr
  refine ⟨?_,?_⟩
  · intro hi
    exact hjm ((fixed_service_path p hi hij) ▸ hi)
  · intro a hai
    exact hij.trans (hjs a (hai.trans hij))

theorem component_universal_source (p : State n) (r : Fin n) (hm : p.symm r ≠ r)
    (hall : ∀ x, p.symm x ≠ x → CycleFootprint.LoadPath (displacement p.symm) r x → FiniteReach p r x) :
    r ∈ sourcePackets p := by
  apply (mem_source_packets p r).mpr
  refine ⟨hm,?_⟩
  intro x hx
  have hxm : p.symm x ≠ x := by
    intro he
    exact hm ((fixed_service_path p he hx) ▸ he)
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  exact hall x hxm (CycleFootprint.load_path_symm _ (CycleFootprint.service_path_load_path hd hx))

theorem bridge_endpoints_in_source_packets (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin k) : (bridgeEndpoints p hc i).1 ∈ sourcePackets p ∧
      (bridgeEndpoints p hc i).2 ∈ sourcePackets p := by
  have hv := ordered_component_bridge_valid p hc i
  have hu : p.symm (bridgeEndpoints p hc i).1 ≠ (bridgeEndpoints p hc i).1 := by
    intro he; have := congrArg Fin.val he; have := hv.2.1; omega
  have hw : p.symm (bridgeEndpoints p hc i).2 ≠ (bridgeEndpoints p hc i).2 := by
    intro he; have := congrArg Fin.val he; have := hv.2.2.1; omega
  constructor
  · apply component_universal_source p _ hu
    intro x hx hp
    apply finite_component_right_reaches p _ (bridgeEndpoints p hc i).2 hu hv.1 _ x hx hp
    intro y hy
    exact component_right_bound p _ y ((component_right_path p _).trans hy)
  · apply component_universal_source p _ hw
    intro x hx hp
    apply finite_component_left_reaches p (bridgeEndpoints p hc i).1 _ hw hv.1 _ x hx hp
    intro y hy
    exact component_left_bound p _ y ((component_left_path p _).trans hy)

theorem joined_source_packets_predecessor_closed (p : State n)
    (hc : (componentRoots p).card=k+1) {i j : Fin n}
    (hp : FiniteReach (joinedComponents p hc) i j) (hj : j ∈ sourcePackets p) :
    i ∈ sourcePackets p := by
  apply bridge_sequence_predecessor_closed p _ (component_bridges_valid p hc)
    (component_bridges_separated p hc) (sourcePackets p) _ (source_packets_predecessor_closed p) hp hj
  intro uv huv
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp huv
  exact bridge_endpoints_in_source_packets p hc a

#print axioms bridge_endpoints_in_source_packets
#print axioms joined_source_packets_predecessor_closed
end LRX.FiniteCuts
