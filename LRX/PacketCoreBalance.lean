import LRX.PacketGapConfinement
import Mathlib

/-! The source packet is balanced even when the load covers the full circle:
all cycles outside it have canonical endpoints after cutting at the root. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

noncomputable def core (p : State n) (d : Fin n → ℤ) (root : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (InCore p d root)


end LRX.PrunedLift
