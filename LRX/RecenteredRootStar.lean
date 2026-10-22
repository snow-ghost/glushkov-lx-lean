import LRX.PeriodicTouches
import LRX.ReducedServiceRoute

/-! Root-star coverage is preserved when coordinates are recentered at a
chosen port. No reachability certificate at the new port is assumed. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_inverse_conjugate (p : State n) (r : Fin n) :
    (localTarget p 0 r)⁻¹=(rotation r)⁻¹*p⁻¹*rotation r := by
  rw [local_target_zero]
  group

theorem same_cycle_recenter (p : State n) (r i j : Fin n) :
    ((localTarget p 0 r)⁻¹).SameCycle i j ↔ (p⁻¹).SameCycle (rotation r i) (rotation r j) := by
  rw [local_inverse_conjugate]
  simpa only [inv_inv] using
    (Equiv.Perm.sameCycle_conj (f := p⁻¹) (g := (rotation r)⁻¹) (x := i) (y := j))

theorem moving_recenter (p : State n) (r i : Fin n) :
    (localTarget p 0 r)⁻¹ i ≠ i ↔ p⁻¹ (rotation r i) ≠ rotation r i := by
  rw [local_inverse_conjugate]
  change (rotation r).symm (p⁻¹ (rotation r i)) ≠ i ↔ _
  constructor
  · intro h he
    apply h
    rw [he,Equiv.symm_apply_apply]
  · intro h he
    apply h
    have hh := congrArg (rotation r) he
    simpa only [Equiv.apply_symm_apply] using hh

theorem rotation_difference_modEq (r i j : Fin n) :
    Int.ModEq (n : ℤ) ((rotation r j : ℤ)-(rotation r i : ℤ)) ((j : ℤ)-(i : ℤ)) := by
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,
    rotation,AffineLift.rotation_power_apply]
  abel

theorem touches_recenter (d : Fin n → ℤ) (r i j : Fin n) :
    BufferProgram.Touches (n : ℤ) (i : ℤ) (localDisplacement d r i) (j : ℤ) ↔
      BufferProgram.Touches (n : ℤ) (rotation r i : ℤ) (d (rotation r i)) (rotation r j : ℤ) :=
  BufferProgram.touches_modEq_iff (rotation_difference_modEq r i j).symm

theorem service_edge_recenter (p : State n) (d : Fin n → ℤ) (r i j : Fin n) :
    BufferProgram.ServiceEdge (localTarget p 0 r) (localDisplacement d r) i j ↔
      BufferProgram.ServiceEdge p d (rotation r i) (rotation r j) := by
  change (((localTarget p 0 r)⁻¹).SameCycle i j ∨
    ((localTarget p 0 r)⁻¹ j ≠ j ∧ BufferProgram.Touches (n : ℤ) (i : ℤ) (localDisplacement d r i) (j : ℤ))) ↔ _
  rw [same_cycle_recenter,moving_recenter,touches_recenter]
  rfl

theorem root_star_recenter (p : State n) (d : Fin n → ℤ) (r : Fin n)
    (hstar : PrunedLift.RootStar p d r) :
    PrunedLift.RootStar (localTarget p 0 r) (localDisplacement d r) 0 := by
  intro i hi
  change d (rotation r i) ≠ 0 at hi
  obtain ⟨a,j,ha,he,hj⟩ := hstar (rotation r i) hi
  have hz : rotation r 0=r := by simp [rotation,AffineLift.rotation_power_apply]
  refine ⟨(rotation r).symm a,(rotation r).symm j,?_,?_,?_⟩
  · apply (same_cycle_recenter p r 0 _).mpr
    simpa only [hz,Equiv.apply_symm_apply] using ha
  · apply (service_edge_recenter p d r _ _).mpr
    simpa only [Equiv.apply_symm_apply] using he
  · apply (same_cycle_recenter p r _ i).mpr
    simpa only [Equiv.apply_symm_apply] using hj

open scoped BigOperators in
theorem root_star_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hroot : d r ≠ 0) (hstar : PrunedLift.RootStar p d r) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d r := by
  apply exists_exact_service hn r hd hshort hroot
  intro i hi
  exact PrunedLift.root_star_reaches _ _ _ (root_star_recenter p d r hstar) i hi

#print axioms service_edge_recenter
#print axioms root_star_recenter
#print axioms root_star_exact_service
end LRX.RotationWords
