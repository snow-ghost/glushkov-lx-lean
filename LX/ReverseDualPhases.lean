import LX.ReverseDual
import LX.SecondExcess
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.WordReflection
variable {n : ℕ} [NeZero n]

def dualPosition (p : State n) : State n := reflection*p

theorem reverse_dual_raw_offset (p : State n) (i : Fin n) :
    reverseDual p (dualPosition p i)-dualPosition p i=p i-i := by
  have he : reverseDual p (dualPosition p i)=reflection i := by
    simp only [reverseDual,dualPosition,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      reflection_twice,Equiv.symm_apply_apply]
  rw [he]
  simp only [dualPosition,Equiv.Perm.mul_apply,reflection_apply]
  ring

theorem reverse_dual_cyclic_offset (p : State n) (a i : Fin n) :
    cyclicOffset (reverseDual p) (dualPosition p a) (dualPosition p i)=cyclicOffset p a i := by
  simp only [cyclicOffset,reverse_dual_raw_offset]

theorem reverse_dual_height (p : State n) (a : Fin n) :
    height (reverseDual p) (dualPosition p a)=height p a := by
  have hm := cyclic_offset_mass (reverseDual p) (dualPosition p a)
  rw [← Equiv.sum_comp (dualPosition p) (fun i : Fin n =>
    (cyclicOffset (reverseDual p) (dualPosition p a) i : ℤ))] at hm
  simp only [reverse_dual_cyclic_offset] at hm
  rw [cyclic_offset_mass] at hm
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have he := mul_left_cancel₀ hn hm
  omega

theorem reverse_dual_below_count (p : State n) (a : Fin n) (t : ℕ) :
    belowCount (reverseDual p) (dualPosition p a) t=belowCount p a t := by
  classical
  simp only [belowCount,Finset.card_filter]
  rw [← Equiv.sum_comp (dualPosition p) (fun i : Fin n =>
    if (cyclicOffset (reverseDual p) (dualPosition p a) i).val < t then (1 : ℕ) else 0)]
  simp only [reverse_dual_cyclic_offset]

theorem reverse_dual_rank_surplus (p : State n) (a : Fin n) (t : ℕ) :
    rankSurplus (reverseDual p) (dualPosition p a) t=rankSurplus p a t := by
  simp only [rankSurplus,reverse_dual_below_count]

theorem reverse_dual_second_excess (p : State n) (a : Fin n) :
    secondExcess (reverseDual p) (dualPosition p a)=secondExcess p a := by
  simp only [secondExcess,reverse_dual_rank_surplus]

theorem reverse_dual_minimum_height (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    ∀ b,height (reverseDual p) (dualPosition p a) ≤ height (reverseDual p) b := by
  intro b
  obtain ⟨c,rfl⟩ := (dualPosition p).surjective b
  rw [reverse_dual_height,reverse_dual_height]
  exact hmin c

#print axioms reverse_dual_height
#print axioms reverse_dual_rank_surplus
#print axioms reverse_dual_second_excess
#print axioms reverse_dual_minimum_height
end LX.AnchoredPhases
