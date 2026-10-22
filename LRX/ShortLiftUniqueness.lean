import LRX.CapacityEqualityReflection

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Two strictly short lifts of the same phase target agree coordinatewise. -/
theorem strict_short_lift_unique {p : State n} {phase : ℤ} {d e : Fin n → ℤ}
    (hd : AffineLift.IsLift p phase d) (he : AffineLift.IsLift p phase e)
    (hdshort : ∀ i, 2*|d i| < (n : ℤ)) (heshort : ∀ i, 2*|e i| < (n : ℤ)) : d=e := by
  let h : ℤ := (((n-1)/2 : ℕ) : ℤ)
  have hD := clockwise_representative_unique (shiftedLiftPermutation p phase h)
    (fun i : Fin n => (i : ℤ)+d i+h)
    (fun i => by have := strict_short_strip d hdshort i; dsimp [h]; omega)
    (shifted_lift_permutation_modEq hd h)
  have hE := clockwise_representative_unique (shiftedLiftPermutation p phase h)
    (fun i : Fin n => (i : ℤ)+e i+h)
    (fun i => by have := strict_short_strip e heshort i; dsimp [h]; omega)
    (shifted_lift_permutation_modEq he h)
  funext i
  have hi := congrFun (hD.trans hE.symm) i
  omega

#print axioms strict_short_lift_unique
end LRX.FiniteCuts
