import LRX.LoadPathRecenter

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Rotating coordinates preserves the number of vertices in a load component. -/
theorem load_component_card_recenter (d : Fin n → ℤ) (r a : Fin n) :
    (CycleFootprint.component (localDisplacement d r) a).card=
      (CycleFootprint.component d (a+r)).card := by
  classical
  refine Finset.card_bij (fun i _ => i+r) ?_ ?_ ?_
  · intro i hi
    apply (CycleFootprint.mem_component _ _ _).mpr
    apply (load_path_recenter d r a i).mp
    exact (CycleFootprint.mem_component _ _ _).mp hi
  · intro i hi j hj hij
    exact add_right_cancel hij
  · intro j hj
    refine ⟨j-r,?_,sub_add_cancel j r⟩
    apply (CycleFootprint.mem_component _ _ _).mpr
    apply (load_path_recenter d r a (j-r)).mpr
    simpa only [sub_add_cancel] using (CycleFootprint.mem_component _ _ _).mp hj

#print axioms load_component_card_recenter
end LRX.RotationWords
