import LRX.ArbitraryFiniteRouteTransfer
import LRX.ShallowContraction

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

def componentBridge (p : State n) (u v : Fin n) : State n := Equiv.swap u v*p

theorem component_bridge_rank (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (hab : (p.symm u).val ≤ (p.symm v).val) : FiniteRankOrder.Below p (componentBridge p u v) := by
  apply (FiniteRankOrder.below_inverse_iff p (componentBridge p u v)).mp
  have hh := FiniteRankOrder.below_raising_swap p⁻¹ u v huv hab
  simpa only [componentBridge,mul_inv_rev,Equiv.Perm.inv_def,Equiv.symm_swap] using hh

theorem component_bridge_inverse (p : State n) (u v i : Fin n) :
    (componentBridge p u v).symm i=p.symm (Equiv.swap u v i) := by
  rfl

theorem component_bridge_mass (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val) :
    (∑ i, |displacement (componentBridge p u v).symm i|)=
      (∑ i, |displacement p.symm i|)+2*((v : ℤ)-(u : ℤ)) := by
  have hne : u ≠ v := by intro h; subst v; omega
  let A : ℤ := |(p.symm v : ℤ)-(u : ℤ)|-|(p.symm u : ℤ)-(u : ℤ)|
  let B : ℤ := |(p.symm u : ℤ)-(v : ℤ)|-|(p.symm v : ℤ)-(v : ℤ)|
  have point (i : Fin n) : |displacement (componentBridge p u v).symm i|=
      |displacement p.symm i|+(if i=u then A else 0)+(if i=v then B else 0) := by
    simp only [displacement,component_bridge_inverse]
    by_cases hi : i=u
    · subst i
      simp only [Equiv.swap_apply_left,ite_true,ite_eq_right hne,add_zero,A]
      ring
    · by_cases hj : i=v
      · subst i
        simp only [Equiv.swap_apply_right,ite_eq_right hi,ite_true,add_zero,B]
        ring
      · simp only [Equiv.swap_apply_of_ne_of_ne hi hj,ite_eq_right hi,ite_eq_right hj,add_zero]
  rw [Finset.sum_congr rfl (fun i _ => point i)]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have he : A+B=2*((v : ℤ)-(u : ℤ)) := by
    dsimp [A,B]
    rw [abs_of_nonneg (by omega : 0 ≤ (p.symm v : ℤ)-(u : ℤ)),
      abs_of_nonpos (by omega : (p.symm u : ℤ)-(u : ℤ) ≤ 0),
      abs_of_nonpos (by omega : (p.symm u : ℤ)-(v : ℤ) ≤ 0),
      abs_of_nonneg (by omega : 0 ≤ (p.symm v : ℤ)-(v : ℤ))]
    ring
  omega

#print axioms component_bridge_rank
#print axioms component_bridge_mass
end LRX.FiniteCuts
