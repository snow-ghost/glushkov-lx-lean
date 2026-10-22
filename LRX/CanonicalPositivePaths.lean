import LRX.ComponentInterval

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- In the canonical linear load graph an interval is connected exactly when
all its intervening ports have positive load. -/
theorem canonical_load_path_iff (p : State n) (a b : Fin n) (hab : a.val ≤ b.val) :
    CycleFootprint.LoadPath (displacement p) a b ↔
      ∀ r : Fin n, a.val ≤ r.val → r.val < b.val → 0 < portLoad (displacement p) r := by
  constructor
  · intro hp r ha hb
    exact load_path_crossed_port_positive p.symm hp r ha hb
  · intro hpos
    have hp := CycleFootprint.integer_load_path (displacement p) (a : ℤ) (b : ℤ)
      (by exact_mod_cast hab) (by
        intro z ha hb
        have hz0 : 0 ≤ z := le_trans (by positivity) ha
        have hzn : z < n := lt_trans hb (by exact_mod_cast b.isLt)
        have hv : ((z : Fin n).val : ℤ) = z := by
          simp only [Fin.val_intCast]
          rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_eq_of_lt hz0 hzn]
        exact hpos (z : Fin n) (by omega) (by omega))
    simpa only [Int.cast_natCast,Fin.cast_val_eq_self] using hp

#print axioms canonical_load_path_iff
end LRX.FiniteCuts
