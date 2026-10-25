import LX.LiftedScanBridge
import Mathlib

namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A descending neighboring pair in the original integer lift must exchange.
The seam case uses a nonzero periodic offset, rather than a linear-order guess. -/
theorem delete_adjacent_descent (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ)
    (w : List Letter) (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (i : Fin n) (hdesc : d (i+1)+1 < d i) :
    ∃ v : List Letter,(p*Equiv.swap i (i+1))*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by
  have hnext : (i+1).val=(i.val+1)%n := by
    rw [Fin.val_add]
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hi : i.val+1 < n
  · have hj : (i+1).val=i.val+1 := hnext.trans (Nat.mod_eq_of_lt hi)
    let key : LRX.LiftedModel.PairKey n := ⟨i,i+1,0⟩
    have hk : key.Valid := by
      constructor
      · change i.val < (i+1).val
        omega
      · exact dvd_zero _
    have hc : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
        (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift) := by
      dsimp only [key]
      omega
    exact delete_crossing_word hn p d w hp hz key hk hc
  · have hnlast : i.val+1=n := by have := i.isLt; omega
    have hj : i+1=0 := by
      apply Fin.ext
      rw [hnext,hnlast,Nat.mod_self,Fin.val_zero]
    rw [hj] at hdesc
    let key : LRX.LiftedModel.PairKey n := ⟨0,i,-(n : ℤ)⟩
    have hk : key.Valid := by
      constructor
      · change (0 : Fin n).val < i.val
        simp only [Fin.val_zero]
        omega
      · exact dvd_neg.mpr (dvd_refl _)
    have hc : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
        (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift) := by
      dsimp only [key]
      simp only [Fin.val_zero,Nat.cast_zero,zero_add]
      omega
    obtain ⟨v,hv,hlen,hrot⟩ := delete_crossing_word hn p d w hp hz key hk hc
    refine ⟨v,?_,hlen,hrot⟩
    simpa only [key,hj,Equiv.swap_comm (0 : Fin n) i] using hv

#print axioms delete_adjacent_descent
end LX.LiftedScan
