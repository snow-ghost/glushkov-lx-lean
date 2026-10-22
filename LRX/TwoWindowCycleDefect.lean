import LRX.ActualNonunitComponentDefect
import LRX.FiniteDisplacementSum

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Cycle defect in physical finite coordinates. -/
def cycleDefect (p : State n) : ℤ :=
  (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)

theorem cycle_defect_inverse (p : State n) : cycleDefect p.symm=cycleDefect p := by
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  have hs : Equiv.Perm.support p.symm=p.support := Equiv.Perm.support_inv p
  have hk : (Equiv.Perm.cycleFactorsFinset p.symm).card=p.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv p)
    simpa only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val,Equiv.Perm.inv_def] using hh
  simp only [cycleDefect,displacement_mass_inverse,hI,hs,hk]

end LRX.FiniteCuts

namespace LRX.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Two disjoint actual invariant windows covering all moving positions
factor the original permutation exactly. -/
theorem two_matched_windows_product (p : State n) (A B : FillingWindow n)
    (ha : A.Apart B) (hA : A.Matches p) (hB : B.Matches p)
    (hcover : ∀ i, p i ≠ i → Contains A.window i ∨ Contains B.window i) :
    p=permutation A.window A.filling*permutation B.window B.filling := by
  apply Equiv.ext
  intro i
  simp only [Equiv.Perm.mul_apply]
  by_cases hiA : Contains A.window i
  · rw [permutation_outside B.window B.filling i (ha i hiA)]
    obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hiA
    rw [permutation_embed]
    exact hA j
  · by_cases hiB : Contains B.window i
    · obtain ⟨j,rfl⟩ := (contains_iff B.window i).mp hiB
      rw [permutation_embed,permutation_outside A.window A.filling _
        (fun hh => ha _ hh (contains_embed B.window (B.filling j)))]
      exact hB j
    · rw [permutation_outside B.window B.filling i hiB,permutation_outside A.window A.filling i hiA]
      by_contra hh
      exact (hcover i hh).elim hiA hiB

/-- Defect adds for physically disjoint windows: their separation also
supplies the required inversion additivity. -/
theorem cycle_defect_two_windows (A B : FillingWindow n) (ha : A.Apart B) :
    cycleDefect (permutation A.window A.filling*permutation B.window B.filling)=
      cycleDefect A.filling+cycleDefect B.filling := by
  classical
  let a := permutation A.window A.filling
  let b := permutation B.window B.filling
  have hd : a.Disjoint b := by
    intro i
    by_cases hh : Contains A.window i
    · exact Or.inr (permutation_outside B.window B.filling i (ha i hh))
    · exact Or.inl (permutation_outside A.window A.filling i hh)
  have hmass : (∑ i, |displacement (a*b) i|)=
      (∑ i, |displacement A.filling i|)+(∑ i, |displacement B.filling i|) := by
    simp_rw [abs_displacement_mul a b hd]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (displacement_mass A.window A.filling) (displacement_mass B.window B.filling)
  have hI : inversionNumber (a*b)=inversionNumber A.filling+inversionNumber B.filling := by
    rw [inversion_number_mul_window B.window a B.filling (fun i =>
      permutation_outside A.window A.filling _ (fun hh => ha _ hh (contains_embed B.window i)))]
    rw [inversion_number_window]
  have hs : (a*b).support.card=A.filling.support.card+B.filling.support.card := by
    rw [hd.card_support_mul,permutation_support_card,permutation_support_card]
  have hk : (a*b).cycleFactorsFinset.card=A.filling.cycleFactorsFinset.card+B.filling.cycleFactorsFinset.card := by
    rw [hd.cycleFactorsFinset_mul_eq_union,Finset.card_union_of_disjoint hd.disjoint_cycleFactorsFinset,
      permutation_cycle_count,permutation_cycle_count]
  change cycleDefect (a*b)=_
  simp only [cycleDefect,hmass,hI,hs,hk,Nat.cast_add]
  ring

#print axioms two_matched_windows_product
#print axioms cycle_defect_two_windows
end LRX.FiniteWindow
