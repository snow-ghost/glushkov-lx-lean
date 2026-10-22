import LRX.FiniteOuterSource
import LRX.ExteriorBoundaryPorts

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

noncomputable def outerLeft (p : State n) (hc : (componentRoots p).card=k+1) : Fin n :=
  componentLeft p (componentOrder p hc 0)
noncomputable def outerRight (p : State n) (hc : (componentRoots p).card=k+1) : Fin n :=
  componentRight p (componentOrder p hc (Fin.last k))

theorem joined_port_load_mono (p : State n) (hc : (componentRoots p).card=k+1) (port : Fin n) :
    portLoad (displacement p.symm) port ≤ portLoad (displacement (joinedComponents p hc).symm) port := by
  rw [port_load_eq_twice_half,port_load_eq_twice_half]
  have hh := bridge_sequence_half_load p _ (component_bridges_valid p hc) (component_bridges_separated p hc) (port.val+1)
  change halfLoad p.symm (port.val+1) ≤ halfLoad (joinedComponents p hc).symm (port.val+1) at hh
  exact_mod_cast Nat.mul_le_mul_left 2 hh

theorem joined_outer_ports (hn : 2 ≤ n) (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    (outerLeft p hc).val < (outerRight p hc).val ∧
      outerLeft p hc ∈ sourcePackets p ∧ outerRight p hc ∈ sourcePackets p ∧
      2 ≤ portLoad (displacement (joinedComponents p hc).symm) (outerLeft p hc) ∧
      2 ≤ portLoad (displacement (joinedComponents p hc).symm) (outerRight p hc-1) := by
  let e := componentOrder p hc
  have hfirst := component_order_mem p hc 0
  have hlast := component_order_mem p hc (Fin.last k)
  have horder := ordered_component_roots p hfirst hlast (e.strictMono (by change 0 < k; exact hk))
  have hroomL : (componentRight p (e 0)).val+1 < n := by
    have := (componentLeft p (e (Fin.last k))).isLt
    change (componentRight p (e 0)).val < (componentLeft p (e (Fin.last k))).val at horder
    omega
  have hroomR : 0 < (componentLeft p (e (Fin.last k))).val := by
    change (componentRight p (e 0)).val < (componentLeft p (e (Fin.last k))).val at horder
    omega
  obtain ⟨hL,hLzero⟩ := left_component_outer_source hn p ⟨e 0,component_root_moved p _ hfirst⟩ hroomL
  obtain ⟨hR,hRzero⟩ := right_component_outer_source hn p ⟨e (Fin.last k),component_root_moved p _ hlast⟩ hroomR
  have hl := component_left_bound p (e 0) (componentRight p (e 0)) (component_right_path p (e 0))
  have hr := component_right_bound p (e (Fin.last k)) (componentLeft p (e (Fin.last k))) (component_left_path p (e (Fin.last k)))
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hloadL := zero_left_load_right_discount hd (outerLeft p hc)
    (displacement_ne_of_moved p.symm _ ((mem_source_packets p _).mp hL).1) hLzero
  have hloadR := zero_right_load_left_discount hd (outerRight p hc)
    (displacement_ne_of_moved p.symm _ ((mem_source_packets p _).mp hR).1) hRzero
  refine ⟨?_,hL,hR,hloadL.trans (joined_port_load_mono p hc _),hloadR.trans (joined_port_load_mono p hc _)⟩
  change (componentLeft p (e 0)).val < (componentRight p (e (Fin.last k))).val
  change (componentRight p (e 0)).val < (componentLeft p (e (Fin.last k))).val at horder
  omega

#print axioms joined_outer_ports
end LRX.FiniteCuts
