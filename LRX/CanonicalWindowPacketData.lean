import LRX.FiniteAggregatePacketFamily
import LRX.WindowFamilyBridge
import LRX.WindowReachability

namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem canonical_window_displacement (p : State n) (W : Window n b) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) (i : Fin b) :
    FiniteCuts.displacement p.symm (embed W i)=FiniteCuts.displacement filling i := by
  unfold FiniteCuts.displacement
  rw [hmatch]
  simp only [embed,Nat.cast_add]
  ring

theorem canonical_window_packet_data (p : State n) (W : Window n b) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (cycles : List (State b)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hparts : ∀ q ∈ cycles, CyclePart.IsPart q filling)
    (root : Fin n) (hroot : ¬Contains W root) :
    CyclePart.IsPart (cycles.map (fun q => (permutation W q)⁻¹)).prod p ∧
    PrunedLift.KeepsCore p (FiniteCuts.displacement p.symm) root
      (cycles.map (fun q => (permutation W q)⁻¹)).prod.supportᶜ := by
  let targets := cycles.map (fun q => (permutation W q)⁻¹)
  let selected := targets.prod
  have htargets : targets.Pairwise Equiv.Perm.Disjoint :=
    List.pairwise_map.mpr (hdis.imp (fun h => (permutation_disjoint W _ _ h).inv_left.inv_right))
  have hpart : CyclePart.IsPart selected p := by
    apply CyclePart.product targets p htargets
    intro q hq
    obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
    exact CyclePart.inverse (CyclePart.trans (CyclePart.window W (hparts q0 hq0))
      (CyclePart.window_part W filling p.symm hmatch))
  have hsupport (j : Fin n) (hj : j ∈ selected.support) : Contains W j := by
    obtain ⟨q,hq,hm⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hj
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hq
    by_contra h
    have hf : (permutation W q)⁻¹ j=j := by
      change (permutation W q).symm j=j
      rw [permutation_symm]
      exact permutation_outside W q.symm j h
    exact (Equiv.Perm.mem_support.mp hm) hf
  exact ⟨hpart,selected_window_keeps_core W p selected (FiniteCuts.displacement p.symm) filling
    hmatch (canonical_window_displacement p W filling hmatch) root hroot hsupport⟩

#print axioms canonical_window_packet_data
end LRX.FiniteWindow
