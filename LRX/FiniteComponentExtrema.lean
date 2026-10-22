import LRX.FiniteComponentBoundary
import LRX.LoadBoundaryActive
import LRX.LoadComponentSet

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

noncomputable def componentSet (p : State n) (a : Fin n) :=
  CycleFootprint.component (displacement p.symm) a

theorem component_set_nonempty (p : State n) (a : Fin n) : (componentSet p a).Nonempty :=
  ⟨a,(CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl⟩

noncomputable def componentLeft (p : State n) (a : Fin n) : Fin n :=
  (componentSet p a).min' (component_set_nonempty p a)
noncomputable def componentRight (p : State n) (a : Fin n) : Fin n :=
  (componentSet p a).max' (component_set_nonempty p a)

theorem component_left_path (p : State n) (a : Fin n) :
    CycleFootprint.LoadPath (displacement p.symm) a (componentLeft p a) :=
  (CycleFootprint.mem_component _ _ _).mp (Finset.min'_mem _ _)

theorem component_right_path (p : State n) (a : Fin n) :
    CycleFootprint.LoadPath (displacement p.symm) a (componentRight p a) :=
  (CycleFootprint.mem_component _ _ _).mp (Finset.max'_mem _ _)

theorem component_right_bound (p : State n) (a x : Fin n)
    (hx : CycleFootprint.LoadPath (displacement p.symm) a x) : x.val ≤ (componentRight p a).val :=
  Finset.le_max' _ _ ((CycleFootprint.mem_component _ _ _).mpr hx)

theorem component_left_bound (p : State n) (a x : Fin n)
    (hx : CycleFootprint.LoadPath (displacement p.symm) a x) : (componentLeft p a).val ≤ x.val :=
  Finset.min'_le _ _ ((CycleFootprint.mem_component _ _ _).mpr hx)

/-- For two ordered nontrivial components, the actual extremal vertices are
moving and have the incoming-arrow order required by a bridge. -/
theorem component_extreme_bridge_data (p : State n) (a b : CycleFootprint.Active p)
    (horder : (componentRight p a.val).val < (componentLeft p b.val).val) :
    p.symm (componentRight p a.val) ≠ componentRight p a.val ∧
    p.symm (componentLeft p b.val) ≠ componentLeft p b.val ∧
    (p.symm (componentRight p a.val)).val < (componentRight p a.val).val ∧
    (componentLeft p b.val).val < (p.symm (componentLeft p b.val)).val := by
  let u := componentRight p a.val
  let v := componentLeft p b.val
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hau := component_right_path p a.val
  have hbv := component_left_path p b.val
  have hmax : ∀ x, CycleFootprint.LoadPath (displacement p.symm) u x → x.val ≤ u.val := by
    intro x hx
    exact component_right_bound p a.val x (hau.trans hx)
  have hmin : ∀ x, CycleFootprint.LoadPath (displacement p.symm) v x → v.val ≤ x.val := by
    intro x hx
    exact component_left_bound p b.val x (hbv.trans hx)
  have hy : (u+1).val=u.val+1 := Fin.val_add_one_of_lt' (by have := v.isLt; omega)
  have hu : p.symm u ≠ u := by
    apply CycleFootprint.load_boundary_active hd (displacement_short p.symm) a u (u+1) hau (Or.inl rfl)
    intro hh
    have := hmax (u+1) hh
    omega
  let y : Fin n := ⟨v.val-1,by have := v.isLt; omega⟩
  have hyv : y.val+1=v.val := by dsimp [y]; omega
  have hy' : y+1=v := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt' (by have := v.isLt; omega),hyv]
  have hv : p.symm v ≠ v := by
    apply CycleFootprint.load_boundary_active hd (displacement_short p.symm) b v y hbv (Or.inr hy'.symm)
    intro hh
    have := hmin y hh
    omega
  have hau' := hmax (p.symm u) (CycleFootprint.arrow_target_load_path hd u)
  have hbv' := hmin (p.symm v) (CycleFootprint.arrow_target_load_path hd v)
  have hu' : (p.symm u).val ≠ u.val := fun he => hu (Fin.ext he)
  have hv' : (p.symm v).val ≠ v.val := fun he => hv (Fin.ext he)
  change p.symm u ≠ u ∧ p.symm v ≠ v ∧ (p.symm u).val < u.val ∧ v.val < (p.symm v).val
  exact ⟨hu,hv,by omega,by omega⟩

#print axioms component_extreme_bridge_data
end LRX.FiniteCuts
