import LRX.OutsideCycleServices
import LRX.ArrowLoadPaths
import LRX.PortLoadBalance

/-! The least moved vertex of a finite cycle moves right, so its right port
has positive even load. Every outside cycle therefore supplies a saving of two. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem cycle_root_le {q : State n} (hq : q.IsCycle) (i : Fin n) (hi : i ∈ q.support) :
    cycleRoot q ≤ i := by
  classical
  have hne := hq.nonempty_support
  simpa only [cycleRoot,dif_pos hne] using Finset.min'_le q.support i hi

theorem cycle_root_displacement_pos {q : State n} (hq : q.IsCycle) :
    0 < FiniteCuts.displacement q (cycleRoot q) := by
  have hr := cycle_root_mem hq
  have hqr := (Equiv.Perm.apply_mem_support (f := q)).mpr hr
  have hle := cycle_root_le hq (q (cycleRoot q)) hqr
  have hne : (q (cycleRoot q)).val ≠ (cycleRoot q).val :=
    fun h => (Equiv.Perm.mem_support.mp hr) (Fin.ext h)
  unfold FiniteCuts.displacement
  change (cycleRoot q).val ≤ (q (cycleRoot q)).val at hle
  omega

theorem cycle_root_load_ge_two {q : State n} (hq : q.IsCycle) :
    2 ≤ portLoad (FiniteCuts.displacement q) (cycleRoot q) := by
  have hd := cycle_root_displacement_pos hq
  have hpos := CycleFootprint.arrow_edge_positive (FiniteCuts.displacement q) (cycleRoot q)
    (cycleRoot q : ℤ) (by omega) (by omega)
  simp only [Int.cast_natCast,Fin.cast_val_eq_self] at hpos
  exact positive_port_load_ge_two (FiniteCuts.canonical_lift q) (cycleRoot q) hpos

theorem outside_cycle_paid_service (hn : 2 ≤ n) {p q : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0)
    (hroot : p⁻¹ 0 ≠ 0) (hq : q ∈ outsideCycles p d 0) :
    ∃ a : ExactService n, a.service.port=cycleRoot q ∧ a.service.target=q⁻¹ ∧
      a.displacement=PrunedLift.displacement q.support d ∧
      (BufferProgram.rotations a.service.word : ℤ) ≤
        (∑ i : Fin n, |PrunedLift.displacement q.support d i|)-2 := by
  have hc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp hq).1).1
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := outside_cycle_right_service hn hd hcover hroot hq
    (cycleRoot q) (cycle_root_mem hc)
  have hload := cycle_root_load_ge_two hc
  rw [← outside_cycle_displacement hd hcover hroot hq] at hload
  exact ⟨a,ha,ht,hdisp,by omega⟩

#print axioms cycle_root_load_ge_two
#print axioms outside_cycle_paid_service
end LRX.ZeroGap
