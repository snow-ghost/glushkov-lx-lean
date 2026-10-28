import LX.FiniteAdjacentInversions
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Joining arrows across adjacent positions increases finite energy by exactly two. -/
theorem adjacent_boundary_mass_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (ha : (p a).val ≤ a.val) (hb : b.val ≤ (p b).val) :
    (∑ i, |displacement (p*Equiv.swap a b) i|)=(∑ i, |displacement p i|)+2 := by
  classical
  have hab : a ≠ b := by intro hh; have := congrArg Fin.val hh; omega
  let D : ℤ := (p b : ℤ)+(p a : ℤ)-2*(a : ℤ)
  have hpoint (i : Fin n) : |displacement (p*Equiv.swap a b) i|=
      |displacement p i|+(if i=a then D else 0)+(if i=b then 2-D else 0) := by
    by_cases hia : i=a
    · subst i
      simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_left,
        ite_true,hab,ite_false,add_zero,D,abs_eq_max_neg]
      omega
    · by_cases hib : i=b
      · subst i
        simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_right,
          ite_true,hia,ite_false,add_zero,D,abs_eq_max_neg]
        omega
      · simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hia hib,
          hia,hib,ite_false,add_zero]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

/-- The same raising adjacent exchange has exact inversion cost one. -/
theorem adjacent_raising_inversion_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (hp : (p a).val < (p b).val) :
    inversionNumber (p*Equiv.swap a b)=inversionNumber p+1 := by
  have hh := adjacent_swap_inversion_price (p*Equiv.swap a b) a b hadj (by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using hp)
  have he : p*Equiv.swap a b*Equiv.swap a b=p := by simp [mul_assoc]
  rw [he] at hh
  exact hh.symm

#print axioms adjacent_boundary_mass_price
#print axioms adjacent_raising_inversion_price
end LX.Core.FiniteCuts
