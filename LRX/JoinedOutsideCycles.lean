import LRX.JoinedPacketCover
import LRX.OutsideCycleServices

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

noncomputable def fillingCycles (p : State n) : Finset (State n) := by
  classical
  exact (p⁻¹).cycleFactorsFinset.filter (fun q => Disjoint q.support (sourcePackets p))

/-- The individual outside cycles survive unchanged, so their own load profiles
and peak discounts can be reused without loss. -/
theorem joined_outside_cycles (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    ZeroGap.outsideCycles (joinedComponents p hc) (displacement (joinedComponents p hc).symm)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 = fillingCycles p := by
  classical
  ext q
  constructor
  · intro hq
    have hdis := ZeroGap.outside_cycle_avoids_core hq
    rw [joined_core_eq_source_packets p hc hk] at hdis
    obtain ⟨hcy,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hq).1
    apply Finset.mem_filter.mpr
    refine ⟨Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨hcy,?_⟩,hdis⟩
    intro i hi
    have hout : i ∉ sourcePackets p := fun ht => Finset.disjoint_left.mp hdis hi ht
    exact (hact i hi).trans (joined_inverse_outside_packets p hc i hout)
  · intro hq
    obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
    obtain ⟨hcy,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨hcy,?_⟩,?_⟩
    · intro i hi
      have hout : i ∉ sourcePackets p := fun ht => Finset.disjoint_left.mp hdis hi ht
      exact (hact i hi).trans (joined_inverse_outside_packets p hc i hout).symm
    · intro hall
      obtain ⟨i,hi⟩ := hcy.nonempty_support
      have hic := hall hi
      rw [joined_core_eq_source_packets p hc hk] at hic
      exact Finset.disjoint_left.mp hdis hi hic

#print axioms joined_outside_cycles
end LRX.FiniteCuts
