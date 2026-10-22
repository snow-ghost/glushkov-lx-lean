import LRX.ComponentRootCorrespondence
import LRX.SelectedMajorization

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem component_displacement_balance (p : State n) (a : Fin n) :
    (∑ i ∈ componentSet p a, displacement p.symm i) = 0 := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  have hz : portLoad (displacement p.symm) z = 0 := by
    rw [port_load_eq_twice_half]
    have he : z.val+1 = n := by dsimp [z]; have := NeZero.pos n; omega
    rw [he,half_load_end]
    simp
  exact CycleFootprint.component_balanced hd z hz a

/-- Every original arrow of a component is bounded by its actual interval width. -/
theorem component_arrow_length (p : State n) (a i : Fin n) (hi : i ∈ componentSet p a) :
    |displacement p.symm i| ≤ ((componentSet p a).card : ℤ)-1 := by
  have hp := (CycleFootprint.mem_component _ _ _).mp hi
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hpi := hp.trans (CycleFootprint.arrow_target_load_path hd i)
  have hl := component_left_bound p a i hp
  have hr := component_right_bound p a i hp
  have hl' := component_left_bound p a (p.symm i) hpi
  have hr' := component_right_bound p a (p.symm i) hpi
  have hw := component_card_eq_width p a
  unfold displacement
  rw [abs_le]
  constructor <;> omega

/-- A nontrivial component supplies a genuine arrow of each sign. -/
theorem component_signed_arrows (p : State n) (a : Fin n)
    (hc : 2 ≤ (componentSet p a).card) :
    (∃ i ∈ componentSet p a, 0 < displacement p.symm i) ∧
      (∃ i ∈ componentSet p a, displacement p.symm i < 0) := by
  classical
  let l := componentLeft p a
  have hlmem : l ∈ componentSet p a :=
    (CycleFootprint.mem_component _ _ _).mpr (component_left_path p a)
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hpl := (component_left_path p a).trans (CycleFootprint.arrow_target_load_path hd l)
  have hlo := component_left_bound p a (p.symm l) hpl
  have hne := nontrivial_component_left_moved p a hc
  have hnval : (p.symm l).val ≠ l.val := fun h => hne (Fin.ext h)
  have hpos : 0 < displacement p.symm l := by unfold displacement; change l.val ≤ (p.symm l).val at hlo; omega
  refine ⟨⟨l,hlmem,hpos⟩,?_⟩
  by_contra h
  push_neg at h
  have hnon : ∀ i ∈ componentSet p a, 0 ≤ displacement p.symm i := by
    intro i hi
    have hh := h i hi
    omega
  have hs := Finset.sum_pos' hnon ⟨l,hlmem,hpos⟩
  rw [component_displacement_balance] at hs
  omega

#print axioms component_arrow_length
#print axioms component_signed_arrows
end LRX.FiniteCuts
