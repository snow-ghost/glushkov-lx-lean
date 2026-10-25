import LRX.PacketCoverage
import Mathlib

/-! Consecutive packet vertices confine all intermediate lifted endpoints.
Thus the open gap has canonical finite displacements. -/
namespace LRX.PrunedLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def InCore (p : State n) (d : Fin n → ℤ) (root i : Fin n) : Prop :=
  Reaches p d root i ∧ Reaches p d i root


end LRX.PrunedLift
