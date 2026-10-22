import LRX.WindowReplacementDisplacement

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

theorem replace_reversal_port_load_mono (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (r : Fin n) :
    portLoad (displacement p) r ≤ portLoad (displacement (replace W p f Fin.revPerm)) r := by
  rw [port_load_eq_twice_half,port_load_eq_twice_half]
  exact_mod_cast Nat.mul_le_mul_left 2 (replace_reversal_half_load_mono W p f hmatch (r.val+1))

/-- Every old load path survives reversal of an invariant filling. -/
theorem replace_reversal_load_path (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) {a c : Fin n}
    (hp : CycleFootprint.LoadPath (displacement p) a c) :
    CycleFootprint.LoadPath (displacement (replace W p f Fin.revPerm)) a c := by
  have hstep {x y : Fin n} (he : CycleFootprint.LoadedStep (displacement p) x y) :
      CycleFootprint.LoadedStep (displacement (replace W p f Fin.revPerm)) x y := by
    rcases he with ⟨he,hpos⟩ | ⟨he,hpos⟩
    · exact Or.inl ⟨he,hpos.trans_le (replace_reversal_port_load_mono W p f hmatch x)⟩
    · exact Or.inr ⟨he,hpos.trans_le (replace_reversal_port_load_mono W p f hmatch y)⟩
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.tail (hstep he)

theorem replace_reversal_component_subset (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (a : Fin n) :
    CycleFootprint.component (displacement p) a ⊆
      CycleFootprint.component (displacement (replace W p f Fin.revPerm)) a := by
  intro i hi
  exact (CycleFootprint.mem_component _ _ _).mpr
    (replace_reversal_load_path W p f hmatch ((CycleFootprint.mem_component _ _ _).mp hi))

#print axioms replace_reversal_component_subset
end LRX.FiniteWindow
