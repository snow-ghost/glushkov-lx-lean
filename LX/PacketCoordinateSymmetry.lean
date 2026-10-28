import LX.PortRoute
import LX.RecenteredLift
import Mathlib

/-! Coordinate changes preserve majorization and the entire strongly
connected root packet. -/
namespace LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem majorized_comp {d : Fin n → ℤ} (hm : Majorized d) (e : State n) :
    Majorized (fun i => d (e i)) := by
  intro S
  have h := hm (S.image e)
  rw [Finset.card_image_of_injective _ e.injective,
    Finset.sum_image (fun i _ j _ hij => e.injective hij)] at h
  exact h
end LX.Core.AffineLift

namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem majorized_recenter {d : Fin n → ℤ} (hm : AffineLift.Majorized d) (r : Fin n) :
    AffineLift.Majorized (localDisplacement d r) :=
  AffineLift.majorized_comp hm (rotation r)


end LX.Core.RotationWords

namespace LX.Core.WordReflection
open scoped BigOperators
variable {n : ℕ} [NeZero n]

end LX.Core.WordReflection
