import LX.OddCenteredMass
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem perturbed_board_labels (m : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) :
    i+(perturbedBoard m C ρ i : Fin n)=(C : Fin n)-ρ i := by
  unfold perturbedBoard
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
  ring


end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.CenteredLift
variable {n : ℕ} [NeZero n]


end LX.Antipode
