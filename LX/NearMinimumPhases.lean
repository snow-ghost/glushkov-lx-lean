import LX.DepthCrowding
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem crossing_unit_of_width (d : Fin n → ℤ)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (i j : Fin n) : |crossing d i j| ≤ 1 := by
  have hhi := hwidth j i
  have hlo := hwidth i j
  have hv := (j-i).isLt
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hnumlo : -(n : ℤ) ≤ crossingNumerator d i j := by unfold crossingNumerator; omega
  have hnumhi : crossingNumerator d i j < 2*(n : ℤ) := by unfold crossingNumerator; omega
  have hqlo := (Int.le_ediv_iff_mul_le hn).mpr (show (-1 : ℤ)*n ≤ crossingNumerator d i j by omega)
  have hqhi := (Int.ediv_lt_iff_lt_mul hn).mpr (show crossingNumerator d i j < (2 : ℤ)*n by omega)
  rw [abs_le]
  unfold crossing
  omega

theorem displacement_depth_width_bound {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (hwidth : ∀ i j,d i-d j ≤ (n : ℤ))
    (k : ℕ) (i : Fin n) (hk : k ≤ backwardDepth d i) :
    d i+(backwardDepth d i : ℤ) ≤ depthCount d (k+1) := by
  rw [displacement_add_depth hd]
  have hterm (j : Fin n) : ((crossing d i j).toNat : ℤ) ≤
      if k+1 ≤ backwardDepth d j then 1 else 0 := by
    have hc := crossing_unit_of_width d hwidth i j
    by_cases hp : 0 < crossing d i j
    · have hh := crossing_pos_depth_lt d i j hp
      rw [ite_eq_left (by omega : k+1 ≤ backwardDepth d j)]
      have hab := le_abs_self (crossing d i j)
      omega
    · have hz : (crossing d i j).toNat=0 := by omega
      rw [hz,Nat.cast_zero]
      split_ifs <;> norm_num
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j)
  simpa [depthCount] using hh


end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases
