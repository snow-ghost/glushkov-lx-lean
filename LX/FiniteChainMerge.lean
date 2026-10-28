import LX.FiniteDropBudget
import Mathlib

namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

private def invTerm (p : LX.Core.State n) (i j : Fin n) : ℕ :=
  if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0

/-- Erasing an ascending chain vertex increases the finite inversion count
by exactly one when all intervening positions are fixed. -/
theorem head_merge_inversions (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val)
    (hfix : ∀ j : Fin n,0 < j.val → j.val < b.val → p j=j) :
    inversionNumber (p*Equiv.swap 0 b)=inversionNumber p+1 := by
  classical
  let q := p*Equiv.swap 0 b
  have hb0 : b ≠ 0 := Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hb)
  have hq0 : q 0=p b := by simp [q]
  have hqb : q b=b := by simp [q,hhead]
  have hqi (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : q i=p i := by
    simp only [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib]
  have hend (j : Fin n) : invTerm q 0 j+invTerm q b j=
      invTerm p 0 j+invTerm p b j+(if j=b then 1 else 0) := by
    by_cases hj0 : j=0
    · subst j
      simp [invTerm,Ne.symm hb0]
    by_cases hjb : j=b
    · subst j
      simp only [invTerm,hq0,hqb,hhead,Fin.val_zero]
      split_ifs <;> omega
    simp only [invTerm,hq0,hqb,hhead,hqi j hj0 hjb,Fin.val_zero,hjb,ite_false,add_zero]
    have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
    by_cases hjlt : j.val < b.val
    · rw [hfix j hjpos hjlt]
      split_ifs <;> omega
    · have hjne : j.val ≠ b.val := fun he => hjb (Fin.ext he)
      split_ifs <;> omega
  have hother (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) (j : Fin n) :
      invTerm q i j=invTerm p i j := by
    have hipos : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
    by_cases hj0 : j=0
    · subst j
      simp [invTerm]
    by_cases hjb : j=b
    · subst j
      rw [invTerm,invTerm,hqb,hqi i hi0 hib]
      by_cases hil : i.val < b.val
      · rw [hfix i hipos hil]
        split_ifs <;> omega
      · simp only [hil,false_and,ite_false]
    · simp only [invTerm,hqi i hi0 hib,hqi j hj0 hjb]
  let row := fun t : LX.Core.State n => fun i : Fin n => ∑ j,invTerm t i j
  have hrow : row q 0+row q b=row p 0+row p b+1 := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hend j)
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  have hr (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : row q i=row p i := by
    apply Finset.sum_congr rfl
    exact fun j _ => hother i hi0 hib j
  have decomp (t : LX.Core.State n) : inversionNumber t=row t 0+row t b+
      ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row t i := by
    have h0 := Finset.sum_erase_add Finset.univ (row t) (Finset.mem_univ (0 : Fin n))
    have h1 := Finset.sum_erase_add (Finset.univ.erase (0 : Fin n)) (row t)
      (by simp [hb0] : b ∈ Finset.univ.erase (0 : Fin n))
    change (∑ i,row t i)=_
    omega
  have he : (∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row q i)=
      ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row p i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hr i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  rw [decomp q,decomp p,he,hrow]
  omega

theorem head_merge_mass (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val) :
    (∑ i, |displacement (p*Equiv.swap 0 b) i|)=∑ i, |displacement p i| := by
  have hb0 : (0 : Fin n) ≠ b := by intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega
  have hpoint (i : Fin n) :
      |displacement (p*Equiv.swap 0 b) i|+
        (if i=b then (p b : ℤ)-(b : ℤ) else 0)=
      |displacement p i|+(if i=0 then (p b : ℤ)-(b : ℤ) else 0) := by
    by_cases hi0 : i=0
    · subst i
      simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_left,hhead,Fin.val_zero,Nat.cast_zero]
      simp only [sub_zero,abs_of_nonneg (Int.natCast_nonneg _)]
      simp only [hb0,ite_false,ite_true,add_zero]
      omega
    by_cases hib : i=b
    · subst i
      simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_right,hhead,sub_self,abs_zero,
        hi0,ite_false,ite_true,add_zero]
      rw [abs_of_nonneg (by omega)]
      omega
    · simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib,
        hi0,hib,ite_false,add_zero]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  omega

theorem head_merge_drops (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val) :
    descendingPositions (p*Equiv.swap 0 b)=descendingPositions p ∧
      backwardUnits (p*Equiv.swap 0 b)=backwardUnits p := by
  have hpoint (i : Fin n) :
      (((p*Equiv.swap 0 b) i).val < i.val ↔ (p i).val < i.val) ∧
      (((p*Equiv.swap 0 b) i).val+1=i.val ↔ (p i).val+1=i.val) := by
    by_cases hi0 : i=0
    · subst i
      simp
    by_cases hib : i=b
    · subst i
      simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right,hhead]
      omega
    · simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib]
      exact ⟨True.intro,True.intro⟩
  constructor
  · ext i
    simpa only [mem_descendingPositions] using (hpoint i).1
  · ext i
    simpa only [backwardUnits,Finset.mem_filter,Finset.mem_univ,true_and] using (hpoint i).2

#print axioms head_merge_inversions
#print axioms head_merge_mass
#print axioms head_merge_drops
end LX.FiniteDropBudget
