import LX.BackwardDepth
import LX.SweepCarrier
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def atDepth (d : Fin n → ℤ) (j : ℕ) : ℕ := backwardDepth d (j : Fin n)

theorem at_depth_rotate (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ) :
    atDepth (rotate d) j = atDepth d (j+1) := by
  simp only [atDepth, rotate_backward_depth hn, finRotate_apply, Nat.cast_add, Nat.cast_one]

theorem compare_head_tail_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ)
    (hj : 2 ≤ j) (hjn : j < n) : atDepth (compareHead d) j = atDepth d j := by
  have hj0 : (j : Fin n) ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn] at hh
    omega
  have hj1 : (j : Fin n) ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn, Nat.mod_eq_of_lt (by omega : 1 < n)] at hh
    omega
  unfold compareHead
  split_ifs
  · exact exchange_other_depth hn d (j : Fin n) hj0 hj1
  · rfl


def returnWord (d : Fin n → ℤ) : List Letter := sweepWord d (n-1) ++ [.x]


end LX.AffineScan
