import LRX.FiniteRankComparator

namespace LRX.FiniteRankOrder
open scoped BigOperators
variable {n : ℕ}

theorem eq_one_of_below_one (p : State n) (hp : Below p 1) : p=1 := by
  classical
  have hle (i : Fin n) : (p i).val ≤ i.val := by
    have hid : rank (1 : State n) (i.val+1) i.val=0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [Equiv.Perm.one_apply]
      exact if_neg (by omega)
    have h := hp (i.val+1) i.val
    rw [hid] at h
    by_contra hgt
    have hterm := Finset.single_le_sum
      (f := fun j : Fin n => if j.val < i.val+1 ∧ i.val<(p j).val then (1 : ℕ) else 0)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hi : i.val < i.val+1 ∧ i.val<(p i).val := by omega
    simp only [hi,ite_true] at hterm
    change 1 ≤ rank p (i.val+1) i.val at hterm
    omega
  have hfix : ∀ k : ℕ, ∀ i : Fin n, i.val=k → p i=i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      by_cases he : p i=i
      · exact he
      · have hlt : (p i).val<k := by
          have hne : (p i).val ≠ i.val := fun h => he (Fin.ext h)
          have := hle i
          omega
        have hpi := ih (p i).val hlt (p i) rfl
        exact p.injective hpi
  apply Equiv.ext
  intro i
  exact hfix i.val i rfl

noncomputable def compareSequence (p : State n) : List (Fin n × Fin n) → State n
  | [] => p
  | (a,b)::xs => compareSequence (compareAt p a b) xs

theorem below_compare_sequence (p q : State n) (hpq : Below p q)
    (xs : List (Fin n × Fin n)) (hadj : ∀ ab ∈ xs, ab.2.val=ab.1.val+1) :
    Below (compareSequence p xs) (compareSequence q xs) := by
  induction xs generalizing p q with
  | nil => exact hpq
  | cons ab xs ih =>
    apply ih
    · exact below_compare p q hpq ab.1 ab.2 (hadj ab (by simp))
    · intro cd hc
      exact hadj cd (by simp [hc])

/-- A fixed adjacent comparison schedule sorting an upper map also sorts
any map below it. Individual ordered pairs are skipped by compareAt. -/
theorem sorting_transfer (p q : State n) (hpq : Below p q)
    (xs : List (Fin n × Fin n)) (hadj : ∀ ab ∈ xs, ab.2.val=ab.1.val+1)
    (hsorted : compareSequence q xs=1) : compareSequence p xs=1 := by
  apply eq_one_of_below_one
  have h := below_compare_sequence p q hpq xs hadj
  rwa [hsorted] at h

#print axioms eq_one_of_below_one
#print axioms sorting_transfer
end LRX.FiniteRankOrder
