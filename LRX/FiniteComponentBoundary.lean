import LRX.BoundaryComponentRoot
import LRX.FiniteBridgeWord

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem finite_component_right_reaches (p : State n) (u v : Fin n)
    (hu : p.symm u ≠ u) (huv : u.val < v.val)
    (hmax : ∀ x, CycleFootprint.LoadPath (displacement p.symm) u x → x.val ≤ u.val)
    (i : Fin n) (hi : p.symm i ≠ i) (hpath : CycleFootprint.LoadPath (displacement p.symm) u i) :
    FiniteReach p u i := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hy : (u+1).val=u.val+1 := Fin.val_add_one_of_lt' (by have := v.isLt; omega)
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) u (u+1) := by
    intro hp
    have hh := hmax (u+1) hp
    omega
  exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm) ⟨u,hu⟩ (u+1)
    (Or.inl rfl) hout ⟨i,hi⟩ hpath

theorem finite_component_left_reaches (p : State n) (u v : Fin n)
    (hv : p.symm v ≠ v) (huv : u.val < v.val)
    (hmin : ∀ x, CycleFootprint.LoadPath (displacement p.symm) v x → v.val ≤ x.val)
    (i : Fin n) (hi : p.symm i ≠ i) (hpath : CycleFootprint.LoadPath (displacement p.symm) v i) :
    FiniteReach p v i := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  let y : Fin n := ⟨v.val-1,by have := v.isLt; omega⟩
  have hyv : y.val+1=v.val := by dsimp [y]; omega
  have hy : y+1=v := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt' (by have := v.isLt; omega),hyv]
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) v y := by
    intro hp
    have hh := hmin y hp
    dsimp [y] at hh
    omega
  exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm) ⟨v,hv⟩ y
    (Or.inr hy.symm) hout ⟨i,hi⟩ hpath

#print axioms finite_component_right_reaches
#print axioms finite_component_left_reaches
end LRX.FiniteCuts
