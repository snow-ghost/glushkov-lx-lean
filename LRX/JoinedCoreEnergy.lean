import LRX.JoinedOutsideCycles

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem joined_core_energy (p : State n) (hc : (componentRoots p).card=k+1) :
    (∑ i, |PrunedLift.displacement (sourcePackets p) (displacement (joinedComponents p hc).symm) i|)=
    (∑ i, |PrunedLift.displacement (sourcePackets p) (displacement p.symm) i|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ) := by
  have split (d : Fin n → ℤ) :
      (∑ i, |PrunedLift.displacement (sourcePackets p) d i|)+
        (∑ i, |PrunedLift.displacement (sourcePackets p)ᶜ d i|)=∑ i, |d i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact PrunedLift.absolute_partition _ d i
  have hG := split (displacement (joinedComponents p hc).symm)
  have hp := split (displacement p.symm)
  rw [joined_filling_displacement p hc] at hG
  have hm := (joined_components_prices p hc).2.1
  omega

#print axioms joined_core_energy
end LRX.FiniteCuts
