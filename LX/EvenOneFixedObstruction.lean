import LX.FixedCountReflection
import LX.AnchoredPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A unique fixed position is the only maximum-depth position, so its
physical index supplies the last-in-fiber premise of the exact price. -/
theorem one_fixed_last_offset (p : State n) (a : Fin n)
    (hf : (fixedPositions (permutation p a)).card=1) :
    ∀ i : Fin n,p i-i=p a-a → i=a := by
  intro i hi
  have hfix : permutation p a i=i := by
    change p i+(a-p a)=i
    linear_combination hi
  exact Finset.card_le_one.mp hf.le i ((mem_fixedPositions _ _).mpr hfix)
    a ((mem_fixedPositions _ _).mpr (permutation_anchor p a))


end LX.AnchoredPhases
