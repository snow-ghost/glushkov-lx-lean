import LRX.ZeroGapCycleRoots
import LRX.FiniteCycleAvailability
import LRX.ReflectedExactService

/-! Every cycle outside the packet has the canonical finite displacement
in the original coordinates, and both incident exact services are available. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem outside_cycle_avoids_core {p q : State n} {d : Fin n → ℤ} {root : Fin n}
    (hq : q ∈ outsideCycles p d root) : Disjoint q.support (PrunedLift.core p d root) := by
  classical
  obtain ⟨hq,hnot⟩ := Finset.mem_filter.mp hq
  apply Finset.disjoint_left.mpr
  intro i hi hic
  apply hnot
  intro j hj
  exact (PrunedLift.mem_core p d root j).mpr
    (PrunedLift.in_core_same_cycle p d root ((PrunedLift.mem_core p d root i).mp hic)
      ((cycle_root_same_cycle hq hi).symm.trans (cycle_root_same_cycle hq hj)))

theorem outside_cycle_displacement {p q : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0)
    (hroot : p⁻¹ 0 ≠ 0) (hq : q ∈ outsideCycles p d 0) :
    PrunedLift.displacement q.support d=FiniteCuts.displacement q := by
  classical
  have hfactor := (Finset.mem_filter.mp hq).1
  have hdis := outside_cycle_avoids_core hq
  funext i
  by_cases hi : i ∈ q.support
  · have hout : ¬PrunedLift.InCore p d 0 i := fun hc =>
      Finset.disjoint_left.mp hdis hi ((PrunedLift.mem_core p d 0 i).mpr hc)
    have hcan := PrunedLift.outside_core_canonical hd hcover hroot i hout
    have hmatch : q i=p.symm i := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hfactor).2 i hi
    simpa only [PrunedLift.displacement,if_pos hi,FiniteCuts.displacement,hmatch] using hcan
  · have hfix : q i=i := Equiv.Perm.notMem_support.mp hi
    simp [PrunedLift.displacement,hi,FiniteCuts.displacement,hfix]

theorem outside_cycle_right_service (hn : 2 ≤ n) {p q : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0)
    (hroot : p⁻¹ 0 ≠ 0) (hq : q ∈ outsideCycles p d 0) (r : Fin n) (hr : r ∈ q.support) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=q⁻¹ ∧
      a.displacement=PrunedLift.displacement q.support d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement q.support d i|)-
          portLoad (PrunedLift.displacement q.support d) r := by
  rw [outside_cycle_displacement hd hcover hroot hq]
  have hc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hq).1).1
  exact single_cycle_exact_service hn hc.inv (FiniteCuts.canonical_lift q)
    (FiniteCuts.displacement_short q) r
    (FiniteCuts.displacement_ne_of_moved q r (Equiv.Perm.mem_support.mp hr))

theorem outside_cycle_left_service (hn : 2 ≤ n) {p q : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0)
    (hroot : p⁻¹ 0 ≠ 0) (hq : q ∈ outsideCycles p d 0) (r : Fin n) (hr : r ∈ q.support) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=q⁻¹ ∧
      a.displacement=PrunedLift.displacement q.support d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement q.support d i|)-
          portLoad (PrunedLift.displacement q.support d) (r-1) := by
  rw [outside_cycle_displacement hd hcover hroot hq]
  have hc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hq).1).1
  exact WordReflection.single_cycle_exact_left_service hn hc.inv (FiniteCuts.canonical_lift q)
    (FiniteCuts.displacement_short q) r
    (FiniteCuts.displacement_ne_of_moved q r (Equiv.Perm.mem_support.mp hr))

#print axioms outside_cycle_avoids_core
#print axioms outside_cycle_displacement
#print axioms outside_cycle_right_service
#print axioms outside_cycle_left_service
end LRX.ZeroGap
