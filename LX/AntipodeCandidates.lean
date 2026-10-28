import LX.FiniteAdjacentInversions
import LX.WordReflection
import LX.ReflectionLiftLower
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Generation-oriented even candidate; its inverse is the sorting
permutation [1,n-1,0,n-2,...,2]. -/
def even : State n := (LX.Core.WordReflection.reflection*Equiv.swap 1 2).symm

def oddRankValue (m k : ℕ) : ℕ :=
  if k=2 then m+1 else if 3 ≤ k ∧ k ≤ m+1 then k-1 else k

def oddRankInverseValue (m k : ℕ) : ℕ :=
  if k=m+1 then 2 else if 2 ≤ k ∧ k ≤ m then k+1 else k

def oddRank (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) : State n where
  toFun i := ⟨oddRankValue m i.val,by
    have := i.isLt
    unfold oddRankValue
    split_ifs <;> omega⟩
  invFun i := ⟨oddRankInverseValue m i.val,by
    have := i.isLt
    unfold oddRankInverseValue
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    change oddRankInverseValue m (oddRankValue m i.val)=i.val
    unfold oddRankValue oddRankInverseValue
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    change oddRankValue m (oddRankInverseValue m i.val)=i.val
    unfold oddRankValue oddRankInverseValue
    split_ifs <;> omega

/-- Generation-oriented odd candidate. -/
def odd (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) : State n :=
  (LX.Core.WordReflection.reflection*oddRank m hm hn).symm

theorem even_rank_inversions (hn : 3 ≤ n) : inversionNumber (Equiv.swap (1 : Fin n) 2)=1 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hh := adjacent_swap_inversion_price (Equiv.swap (1 : Fin n) 2) 1 2
    (by rw [hv1,hv2]) (by simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,hv1,hv2]; omega)
  have he : (Equiv.swap (1 : Fin n) 2)*Equiv.swap 1 2=1 := Equiv.swap_mul_self _ _
  rw [he] at hh
  have hz : inversionNumber (1 : State n)=0 := by
    unfold inversionNumber
    simp only [Equiv.Perm.one_apply]
    have hp (i j : Fin n) : ¬(i.val < j.val ∧ j.val < i.val) := by omega
    simp only [hp,ite_false,Finset.sum_const_zero]
  omega

theorem odd_rank_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    inversionNumber (oddRank m hm hn)=m-1 := by
  let a : Fin n := ⟨2,by omega⟩
  let b : Fin n := ⟨m+1,by omega⟩
  have hp (i j : Fin n) :
      (i.val < j.val ∧ (oddRank m hm hn j).val < (oddRank m hm hn i).val) ↔
        i=a ∧ a < j ∧ j ≤ b := by
    have hea : i=a ↔ i.val=2 := Fin.ext_iff
    rw [hea]
    change (i.val < j.val ∧ oddRankValue m j.val < oddRankValue m i.val) ↔
      i.val=2 ∧ 2 < j.val ∧ j.val ≤ m+1
    unfold oddRankValue
    split_ifs <;> omega
  unfold inversionNumber
  simp_rw [hp,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hset : (Finset.univ.filter fun j : Fin n => a < j ∧ j ≤ b)=Finset.Ioc a b := by ext; simp
  simp only [← ite_and,Finset.sum_boole,hset,Fin.card_Ioc]
  change m+1-2=m-1
  omega

/-- Uniform exchange lower bound for every lift and every phase of the
even candidate. -/
theorem even_lift_inversions_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : ℤ} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even c d) :
    m*(m-1) ≤ inversions d+1 := by
  have hp (i : Fin n) : (even : State n).symm i=1-(Equiv.swap (1 : Fin n) 2) i := rfl
  have hh := even_reflection_lift_lower hd (Equiv.swap 1 2) hp m hn
  rwa [even_rank_inversions (by omega : 3 ≤ n)] at hh

theorem odd_lift_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : ℤ} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) c d) :
    m^2 ≤ inversions d+(m-1) := by
  have hp (i : Fin n) : (odd m hm hn).symm i=1-(oddRank m hm hn) i := rfl
  have hh := odd_reflection_lift_lower hd (oddRank m hm hn) hp m hn
  rwa [odd_rank_inversions m hm hn] at hh

#print axioms even_lift_inversions_lower
#print axioms odd_lift_inversions_lower
end LX.Antipode
