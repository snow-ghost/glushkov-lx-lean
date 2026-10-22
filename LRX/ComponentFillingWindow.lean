import LRX.ComponentInterval
import LRX.ReversalWindowFamily
import LRX.FiniteWindowRestriction

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Extract an invariant filling from an actual canonical load component. -/
theorem exists_component_filling_window (p : State n) (a : Fin n) :
    ∃ A : FillingWindow n, A.size = (componentSet p a).card ∧
      (∀ i, Contains A.window i ↔ i ∈ componentSet p a) ∧ A.Matches p.symm := by
  classical
  have hlr := component_right_bound p a (componentLeft p a) (component_left_path p a)
  have hw := component_card_eq_width p a
  let W : Window n (componentSet p a).card :=
    ⟨(componentLeft p a).val, by have := (componentRight p a).isLt; omega⟩
  have hW (i : Fin n) : Contains W i ↔ i ∈ componentSet p a := by
    change (componentLeft p a).val ≤ i.val ∧
      i.val < (componentLeft p a).val + (componentSet p a).card ↔ _
    rw [hw, component_set_eq_interval]
    simp only [Finset.mem_Icc, Fin.le_def]
    omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W p (fun i hi => by
    apply (hW _).mpr
    have hp := (CycleFootprint.mem_component _ _ _).mp ((hW i).mp hi)
    exact (CycleFootprint.mem_component _ _ _).mpr
      (hp.trans (CycleFootprint.arrow_target_load_path hd i)))
  exact ⟨⟨(componentSet p a).card,W,f⟩,rfl,hW,hf⟩

#print axioms exists_component_filling_window
end LRX.FiniteCuts
