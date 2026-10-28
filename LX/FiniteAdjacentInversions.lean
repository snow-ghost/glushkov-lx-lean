import LX.FiniteWindowInversions
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem adjacent_swap_inversion_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (hdesc : (p b).val < (p a).val) :
    inversionNumber (p*Equiv.swap a b)+1=inversionNumber p := by
  let τ : State n := Equiv.swap a b
  have hab : a ≠ b := by intro he; have := congrArg Fin.val he; omega
  have point (i j : Fin n) :
      (if (τ i).val < (τ j).val ∧ (p j).val < (p i).val then (1 : ℕ) else 0)+
        (if i=a ∧ j=b then 1 else 0)=
      (if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0) := by
    have hiaval : i.val=a.val ↔ i=a := Fin.ext_iff.symm
    have hibval : i.val=b.val ↔ i=b := Fin.ext_iff.symm
    have hjaval : j.val=a.val ↔ j=a := Fin.ext_iff.symm
    have hjbval : j.val=b.val ↔ j=b := Fin.ext_iff.symm
    dsimp [τ]
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      by_cases hja : j=a <;> by_cases hjb : j=b
    all_goals simp only [Equiv.swap_apply_def,hia,hib,hja,hjb,ite_true,ite_false]
    all_goals try subst i
    all_goals try subst j
    all_goals simp only [hab,Ne.symm hab,ite_false,true_and,false_and,and_true,and_false,ite_true,add_zero]
    all_goals try have hia' : i.val ≠ a.val := fun he => hia (Fin.ext he)
    all_goals try have hib' : i.val ≠ b.val := fun he => hib (Fin.ext he)
    all_goals try have hja' : j.val ≠ a.val := fun he => hja (Fin.ext he)
    all_goals try have hjb' : j.val ≠ b.val := fun he => hjb (Fin.ext he)
    all_goals split_ifs <;> omega
  have hreindex : inversionNumber (p*τ)=
      ∑ i : Fin n, ∑ j : Fin n, if (τ i).val < (τ j).val ∧ (p j).val < (p i).val then 1 else 0 := by
    unfold inversionNumber
    rw [← Equiv.sum_comp τ (fun i => ∑ j : Fin n,
      if i.val < j.val ∧ ((p*τ) j).val < ((p*τ) i).val then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp τ (fun j =>
      if (τ i).val < j.val ∧ ((p*τ) j).val < ((p*τ) (τ i)).val then (1 : ℕ) else 0)]
    simp only [Equiv.Perm.mul_apply,τ,Equiv.swap_apply_self]
  have hsum := congrArg (fun g : Fin n → Fin n → ℕ => ∑ i, ∑ j, g i j) (funext fun i => funext (point i))
  simp only [Finset.sum_add_distrib] at hsum
  have hone : (∑ i : Fin n, ∑ j : Fin n, if i=a ∧ j=b then (1 : ℕ) else 0)=1 := by
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero]
  rw [hone] at hsum
  rw [hreindex]
  exact hsum

#print axioms adjacent_swap_inversion_price
end LX.Core.FiniteCuts
