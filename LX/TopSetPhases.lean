import LX.PhaseExchangePrice
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Equal displacement values may be split between the two sides of a phase
cut. Such a split can give width exactly n and need not be an anchored lift. -/
def IsTopSet (d : Fin n → ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S,∀ j ∉ S,d j ≤ d i


/-- The additive penalty is exact even for a split of a tied displacement. -/
def phasePenalty (d : Fin n → ℤ) (S : Finset (Fin n)) : ℤ :=
  (S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i

theorem phase_penalty_nonneg {d : Fin n → ℤ} (hm : Majorized d)
    (S : Finset (Fin n)) : 0 ≤ phasePenalty d S := by
  have hh := hm S
  unfold phasePenalty
  omega

theorem top_phase_exchange_price {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (hm : Majorized d) (S : Finset (Fin n))
    (htop : IsTopSet d S) :
    inversions (phaseShift d S)=inversions d+(phasePenalty d S).toNat := by
  have hw (i j : Fin n) : d i-d j < (n : ℤ) := by
    have := range_bound hd.1 hm i j
    omega
  have he := top_phase_inversions hd S hw htop
  have hp := phase_penalty_nonneg hm S
  change (inversions (phaseShift d S) : ℤ)-inversions d=phasePenalty d S at he
  omega


#print axioms top_phase_exchange_price
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases
