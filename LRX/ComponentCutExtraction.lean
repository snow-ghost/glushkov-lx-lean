import LRX.ComponentInterval

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Moving the origin to an actual component's left endpoint exposes an
invariant prefix whose size is exactly that component's cardinality. -/
theorem component_recenter_cut (p : State n) (a : Fin n) :
    let r := componentLeft p a
    let q := localTarget p 0 r
    (∀ i : Fin n, (q i).val < (componentSet p a).card ↔
      i.val < (componentSet p a).card) ∧
    (∀ i : Fin n, (componentSet q i).card = (componentSet p (i+r)).card) := by
  let r := componentLeft p a
  let z := r-1
  let q := localTarget p 0 r
  have hz : portLoad (displacement p.symm) z = 0 := component_left_port_zero p a
  have hzr : z+1 = r := by dsimp [z]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hcan := phase_zero_cut_canonical 0 z hd hz
  rw [hzr] at hcan
  have hle : r.val ≤ (componentRight p a).val :=
    component_left_bound p a _ (component_right_path p a)
  let t := componentRight p a-r
  have htval : t.val+1 = (componentSet p a).card := by
    dsimp only [t]
    rw [Fin.sub_val_of_le hle,component_card_eq_width]
    change (componentRight p a).val-r.val+1 = (componentRight p a).val+1-r.val
    omega
  have htz := zero_cut_target_load p z t hz
  rw [hzr] at htz
  have htr : t+r = componentRight p a := sub_add_cancel _ _
  rw [htr,component_right_port_zero] at htz
  have hcut := zero_port_invariant_cut q t htz
  rw [htval] at hcut
  refine ⟨hcut,?_⟩
  intro i
  change (CycleFootprint.component (displacement q.symm) i).card =
    (CycleFootprint.component (displacement p.symm) (i+r)).card
  rw [← hcan]
  exact load_component_card_recenter _ r i

#print axioms component_recenter_cut
end LRX.FiniteCuts
