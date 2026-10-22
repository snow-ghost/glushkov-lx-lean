import LRX.PacketSquareEnvelope
import LRX.InternalGapLoad

/-! Every actual internal-gap price is paid once the packet exchange reserve
is established. All geometric and quadratic premises are derived from the lift. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

theorem internal_gap_payment {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ internalStarts p d) (K : ℕ)
    (hK : 2*gapEnergy p d a+(K : ℤ)^2 ≤ (size (PrunedLift.core p d 0) a : ℤ)^2)
    (delta : ℤ) (hdelta : (PrunedLift.coreHalfSize p d : ℤ)-1 ≤ delta) :
    (K : ℤ)-RotationWords.portLoad d a ≤ delta+epsilon d := by
  classical
  exact CayleyPy.ConnectedComplementCap.all_internal_gaps_paid
    (PrunedLift.coreHalfSize p d) delta (epsilon d) K (RotationWords.portLoad d a) (squareEnvelope p d)
    (by positivity) hdelta (epsilon_nonneg hd hm)
    (internal_load_ge_two hd a (Finset.mem_filter.mp ha).2)
    (localized_gap_energy hd hcover hroot a ha K hK)
    (square_envelope_cap hd hm hcover hroot)

#print axioms internal_gap_payment
end LRX.FiniteGaps
