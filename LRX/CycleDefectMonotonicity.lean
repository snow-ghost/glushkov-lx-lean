import LRX.TwoWindowCycleDefect
import LRX.PrunedPartition

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Pairwise order disagreement satisfies the triangle inequality under composition. -/
theorem inversion_disagreement_triangle (p q : State n) (i j : Fin n) :
    inversionIndicator (p*q) i j+inversionIndicator (p*q) j i ≤
      inversionIndicator q i j+inversionIndicator q j i+
      inversionIndicator p (q i) (q j)+inversionIndicator p (q j) (q i) := by
  by_cases he : i=j
  · subst j
    simp
  have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
  have hqne : (q i).val ≠ (q j).val := fun h => he (q.injective (Fin.ext h))
  have hpne : (p (q i)).val ≠ (p (q j)).val := fun h => he (q.injective (p.injective (Fin.ext h)))
  unfold inversionIndicator
  simp only [Equiv.Perm.mul_apply]
  split_ifs <;> omega

/-- Ordinary finite inversion number is subadditive under composition. -/
theorem inversion_number_mul_le (p q : State n) :
    inversionNumber (p*q) ≤ inversionNumber p+inversionNumber q := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => inversion_disagreement_triangle p q i j))
  have hswap (r : State n) : (∑ i, ∑ j, inversionIndicator r j i)=(inversionNumber r : ℤ) := by
    rw [Finset.sum_comm,sum_inversion_indicator]
  have hqsum : (∑ i, ∑ j, inversionIndicator p (q i) (q j))=(inversionNumber p : ℤ) := by
    calc
      _ = ∑ i, ∑ j, inversionIndicator p i (q j) :=
        Equiv.sum_comp q (fun i => ∑ j, inversionIndicator p i (q j))
      _ = ∑ i, ∑ j, inversionIndicator p i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp q (fun j => inversionIndicator p i j)
      _ = _ := sum_inversion_indicator p
  have hqswap : (∑ i, ∑ j, inversionIndicator p (q j) (q i))=(inversionNumber p : ℤ) := by
    rw [Finset.sum_comm]
    exact hqsum
  simp only [Finset.sum_add_distrib,sum_inversion_indicator,hswap,hqsum,hqswap] at hh
  omega

/-- Disjoint factors have additive mass and cycle rank, so their defects
sum to at most the defect of the product. -/
theorem cycle_defect_disjoint_superadditive (p q : State n) (hd : p.Disjoint q) :
    cycleDefect p+cycleDefect q ≤ cycleDefect (p*q) := by
  classical
  have hi := inversion_number_mul_le p q
  have hm : (∑ i, |displacement (p*q) i|)=
      (∑ i, |displacement p i|)+(∑ i, |displacement q i|) := by
    simp_rw [abs_displacement_mul p q hd]
    rw [Finset.sum_add_distrib]
  have hk : (p*q).cycleFactorsFinset.card=p.cycleFactorsFinset.card+q.cycleFactorsFinset.card := by
    rw [hd.cycleFactorsFinset_mul_eq_union,Finset.card_union_of_disjoint hd.disjoint_cycleFactorsFinset]
  unfold cycleDefect
  rw [hm,hd.card_support_mul,hk]
  push_cast
  omega

/-- Every invariant pruned factor inherits zero cycle defect from the original map. -/
theorem zero_defect_pruned_factor (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hz : cycleDefect p=0) :
    cycleDefect (PrunedLift.permutation p S hS)=0 := by
  let q := PrunedLift.permutation p S hS
  let r := PrunedLift.permutation p Sᶜ (PrunedLift.complement_invariant p S hS)
  have hd := PrunedLift.permutation_disjoint p S hS
  have hp := PrunedLift.permutation_partition p S hS
  have hh := cycle_defect_disjoint_superadditive q r hd
  have hq := finite_depth_rank q
  have hr := finite_depth_rank r
  change q*r=p at hp
  rw [hp,hz] at hh
  change cycleDefect q=0
  unfold cycleDefect at *
  omega

#print axioms inversion_number_mul_le
#print axioms cycle_defect_disjoint_superadditive
#print axioms zero_defect_pruned_factor
end LRX.FiniteCuts
