import LX.MinimumHeightRanks
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

def secondExcess (p : State n) (a : Fin n) : ℤ :=
  ∑ t : Fin n, max (rankSurplus p a t.val-2) 0

theorem second_excess_count (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    2*secondExcess p a =
      2*((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ)-
      2*((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ)+
      (n : ℤ)*((n : ℤ)-3-2*height p a) := by
  classical
  have he (t : Fin n) : max (rankSurplus p a t.val-2) 0 =
      rankSurplus p a t.val-1+(if rankSurplus p a t.val=0 then 1 else 0)-
        (if 2 ≤ rankSurplus p a t.val then 1 else 0) := by
    have := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
    split_ifs <;> omega
  unfold secondExcess
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hs := rank_surplus_sum p a
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hz : (∑ t : Fin n,if rankSurplus p a t.val=0 then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ) := by simp
  have hp : (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ) := by simp
  rw [hz,hp]
  nlinarith


#print axioms second_excess_count
end LX.AnchoredPhases
