import LRX.CyclicCutTargets

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

noncomputable def zeroCutPorts (p : State n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun z => portLoad (displacement p.symm) z=0)

theorem zero_cut_ports_nonempty (p : State n) : (zeroCutPorts p).Nonempty := by
  classical
  let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  have hz : z.val+1=n := by dsimp [z]; have := NeZero.pos n; omega
  refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  rw [port_load_eq_twice_half,hz,half_load_end]
  simp

/-- Choose a zero cut whose outside width cannot be increased by any further
zero-cut recentering. This is a maximum over actual cyclic conjugates. -/
theorem exists_maximum_zero_cut (p : State n) :
    ∃ z : Fin n, portLoad (displacement p.symm) z=0 ∧
      ∀ t : Fin n, portLoad (displacement (localTarget p 0 (z+1)).symm) t=0 →
        externalWidth (localTarget (localTarget p 0 (z+1)) 0 (t+1)) ≤
          externalWidth (localTarget p 0 (z+1)) := by
  classical
  obtain ⟨z,hz,hmax⟩ := Finset.exists_mem_eq_sup (zeroCutPorts p) (zero_cut_ports_nonempty p)
    (fun z => externalWidth (localTarget p 0 (z+1)))
  have hz0 := (Finset.mem_filter.mp hz).2
  refine ⟨z,hz0,?_⟩
  intro t ht
  rw [zero_cut_target_load p z t hz0] at ht
  have hmem : t+(z+1) ∈ zeroCutPorts p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
  have hb := Finset.le_sup (f := fun z => externalWidth (localTarget p 0 (z+1))) hmem
  rw [hmax] at hb
  have he : (z+1)+(t+1)=(t+(z+1))+1 := by abel
  rw [local_target_recenter_twice,he]
  exact hb

#print axioms exists_maximum_zero_cut
end LRX.FiniteCuts
