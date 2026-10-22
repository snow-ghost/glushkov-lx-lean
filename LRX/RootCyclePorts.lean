import LRX.ReflectedRootStar

/-! Every vertex of the same nontrivial root cycle can serve as root. -/
namespace LRX.PrunedLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem root_star_same_cycle (p : State n) (d : Fin n → ℤ) (a b : Fin n)
    (hstar : RootStar p d a) (hc : (p⁻¹).SameCycle a b) : RootStar p d b := by
  intro i hi
  obtain ⟨s,j,hs,he,hj⟩ := hstar i hi
  exact ⟨s,j,hc.symm.trans hs,he,hj⟩

variable [NeZero n]

theorem nonzero_same_cycle {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (a b : Fin n)
    (ha : d a ≠ 0) (hc : (p⁻¹).SameCycle a b) : d b ≠ 0 := by
  have hma : p⁻¹ a ≠ a := fun h => ha (BufferProgram.fixed_short_displacement hd a (hshort a) h)
  have hmb : p⁻¹ b ≠ b := fun h => hma (hc.apply_eq_self_iff.mpr h)
  intro hb
  have h := AffineLift.lift_residue hd b
  simp only [hb,Int.cast_zero,add_zero] at h
  exact hmb h.symm

#print axioms root_star_same_cycle
#print axioms nonzero_same_cycle
end LRX.PrunedLift
