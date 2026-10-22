import LRX.MaximumSeparatorBound

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem loaded_step_recenter (d : Fin n → ℤ) (r i j : Fin n) :
    CycleFootprint.LoadedStep (localDisplacement d r) i j ↔
      CycleFootprint.LoadedStep d (i+r) (j+r) := by
  simp only [CycleFootprint.LoadedStep,port_load_recenter]
  constructor
  · rintro (⟨h,hp⟩ | ⟨h,hp⟩)
    · exact Or.inl ⟨by linear_combination h,hp⟩
    · exact Or.inr ⟨by linear_combination h,hp⟩
  · rintro (⟨h,hp⟩ | ⟨h,hp⟩)
    · exact Or.inl ⟨by linear_combination h,hp⟩
    · exact Or.inr ⟨by linear_combination h,hp⟩

theorem load_path_recenter_inverse (d : Fin n → ℤ) (r : Fin n) {a b : Fin n}
    (hp : CycleFootprint.LoadPath d a b) :
    CycleFootprint.LoadPath (localDisplacement d r) (a-r) (b-r) := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hp he ih =>
    apply ih.tail
    apply (loaded_step_recenter d r (b-r) (c-r)).mpr
    simpa only [sub_add_cancel] using he

theorem load_path_recenter (d : Fin n → ℤ) (r i j : Fin n) :
    CycleFootprint.LoadPath (localDisplacement d r) i j ↔
      CycleFootprint.LoadPath d (i+r) (j+r) := by
  constructor
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail ((loaded_step_recenter d r _ _).mp he)
  · intro hp
    simpa only [add_sub_cancel_right] using load_path_recenter_inverse d r hp

#print axioms load_path_recenter
end LRX.RotationWords
