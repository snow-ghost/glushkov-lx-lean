import LRX.BridgeSequenceReach

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem joined_component_cross (p : State n) (hc : (componentRoots p).card=k+1) (i : Fin k) :
    FiniteReach (joinedComponents p hc) (bridgeEndpoints p hc i).1 (bridgeEndpoints p hc i).2 := by
  exact (bridge_sequence_cross_reach p _ (component_bridges_valid p hc)
    (component_bridges_separated p hc) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).1

theorem joined_component_right_reaches (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin k) (x : Fin n) (hx : p.symm x ≠ x)
    (hp : CycleFootprint.LoadPath (displacement p.symm) (componentOrder p hc i.castSucc) x) :
    FiniteReach (joinedComponents p hc) (bridgeEndpoints p hc i).1 x := by
  have hv := ordered_component_bridge_valid p hc i
  have hu : p.symm (bridgeEndpoints p hc i).1 ≠ (bridgeEndpoints p hc i).1 := by
    intro he
    have := congrArg Fin.val he
    have := hv.2.1
    omega
  apply bridge_sequence_preserves_reach p _ (component_bridges_valid p hc) (component_bridges_separated p hc)
  apply finite_component_right_reaches p _ (bridgeEndpoints p hc i).2 hu hv.1
  · intro y hy
    exact component_right_bound p _ y ((component_right_path p _).trans hy)
  · exact hx
  · exact (CycleFootprint.load_path_symm _ (component_right_path p _)).trans hp

theorem joined_component_left_reaches (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin k) (x : Fin n) (hx : p.symm x ≠ x)
    (hp : CycleFootprint.LoadPath (displacement p.symm) (componentOrder p hc i.succ) x) :
    FiniteReach (joinedComponents p hc) (bridgeEndpoints p hc i).2 x := by
  have hv := ordered_component_bridge_valid p hc i
  have hu : p.symm (bridgeEndpoints p hc i).2 ≠ (bridgeEndpoints p hc i).2 := by
    intro he
    have := congrArg Fin.val he
    have := hv.2.2.1
    omega
  apply bridge_sequence_preserves_reach p _ (component_bridges_valid p hc) (component_bridges_separated p hc)
  apply finite_component_left_reaches p (bridgeEndpoints p hc i).1 _ hu hv.1
  · intro y hy
    exact component_left_bound p _ y ((component_left_path p _).trans hy)
  · exact hx
  · exact (CycleFootprint.load_path_symm _ (component_left_path p _)).trans hp

/-- A forward induction crosses every bridge; no reverse reachability of an
arbitrary representative inside its component is assumed. -/
theorem joined_component_chain (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (i : Fin k) : FiniteReach (joinedComponents p hc)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 (bridgeEndpoints p hc i).2 := by
  have h : ∀ t (ht : t < k), FiniteReach (joinedComponents p hc)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 (bridgeEndpoints p hc ⟨t,ht⟩).2 := by
    intro t
    induction t with
    | zero => intro ht; exact joined_component_cross p hc ⟨0,ht⟩
    | succ t ih =>
      intro ht
      let a : Fin k := ⟨t,by omega⟩
      let b : Fin k := ⟨t+1,ht⟩
      have he : a.succ=b.castSucc := Fin.ext rfl
      have hv := ordered_component_bridge_valid p hc b
      have hm : p.symm (bridgeEndpoints p hc b).1 ≠ (bridgeEndpoints p hc b).1 := by
        intro hh
        have := congrArg Fin.val hh
        have := hv.2.1
        omega
      have hp : CycleFootprint.LoadPath (displacement p.symm) (componentOrder p hc a.succ)
          (bridgeEndpoints p hc b).1 := by
        rw [he]
        exact component_right_path p _
      exact ((ih a.isLt).trans (joined_component_left_reaches p hc a _ hm hp)).trans
        (joined_component_cross p hc b)
  exact h i.val i.isLt

theorem joined_components_all_reached (p : State n) (hc : (componentRoots p).card=k+1)
    (hk : 0 < k) (x : Fin n) (hx : (joinedComponents p hc).symm x ≠ x) :
    FiniteReach (joinedComponents p hc) (bridgeEndpoints p hc ⟨0,hk⟩).1 x := by
  have hs := bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)
  have hm : p.symm x ≠ x := by
    apply (mem_support_inverse p x).mp
    rw [← hs]
    exact (mem_support_inverse (joinedComponents p hc) x).mpr hx
  obtain ⟨a,ha,hpath⟩ := component_roots_cover p x hm
  obtain ⟨j,hj⟩ := component_order_surjective p hc a ha
  rw [← hj] at hpath
  by_cases hz : j.val=0
  · have hj0 : j=(⟨0,hk⟩ : Fin k).castSucc := Fin.ext hz
    rw [hj0] at hpath
    exact joined_component_right_reaches p hc ⟨0,hk⟩ x hm hpath
  · let i : Fin k := ⟨j.val-1,by have := j.isLt; omega⟩
    have hij : i.succ=j := Fin.ext (by dsimp [i]; omega)
    rw [← hij] at hpath
    exact (joined_component_chain p hc hk i).trans (joined_component_left_reaches p hc i x hm hpath)

#print axioms joined_components_all_reached
end LRX.FiniteCuts
