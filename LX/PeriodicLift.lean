import LX.AffineLift
import Mathlib

/-! Integer residues and normalization of the phase of a balanced lift.
The normalized phase is represented by an element of `Fin n`. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

theorem residue_val (z : ℤ) : ((Fin.intCast z : Fin n) : ℤ) = z % (n : ℤ) := by
  change ((z : Fin n).val : ℤ) = _
  rw [Fin.val_intCast]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt modulus_pos))

theorem modEq_residue (z : ℤ) :
    Int.ModEq (n : ℤ) z ((Fin.intCast z : Fin n) : ℤ) := by
  rw [residue_val]
  simp [Int.ModEq]

theorem normalize_phase {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : IsLift p ((Fin.intCast c : Fin n) : ℤ) d := by
  refine ⟨hd.1, ?_⟩
  intro i
  exact (hd.2 i).trans ((modEq_residue c).add_left (p.symm i : ℤ))


end LX.Core.AffineLift
