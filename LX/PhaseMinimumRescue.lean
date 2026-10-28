import LX.AffineLift
import LX.WordMetric
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

def raiseMinimum (d : Fin n → ℤ) (a : Fin n) : Fin n → ℤ :=
  phaseShift d (Finset.univ.erase a)

theorem raise_minimum_apply (d : Fin n → ℤ) (a i : Fin n) :
    raiseMinimum d a i=d i-1+if i=a then (n : ℤ) else 0 := by
  have hn : 1 ≤ n := NeZero.pos n
  unfold raiseMinimum phaseShift
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,Finset.mem_erase,Finset.mem_univ,and_true]
  by_cases hi : i=a <;> simp [hi] <;> ring

theorem raise_minimum_lift {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) :
    IsLift p (c+(n : ℤ)-1) (raiseMinimum d a) := by
  have hh := shift_lift hd (Finset.univ.erase a)
  have hn : 1 ≤ n := NeZero.pos n
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,raiseMinimum,add_sub_assoc] using hh


end LX.AffineScan
