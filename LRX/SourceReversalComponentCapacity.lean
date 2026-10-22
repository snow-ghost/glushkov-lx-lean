import LRX.SourceReversalComponentEquality
import LRX.ComponentInversionBudget

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Exact joint price needs no shortness or width bound. -/
theorem reverse_windows_inversion_price (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p) (hapart : As.Pairwise FillingWindow.Apart) :
    (inversionNumber (reverseWindows As p) : ℤ) =
      (inversionNumber p : ℤ) + (As.map FillingWindow.deficit).sum := by
  induction As generalizing p with
  | nil => simp [reverseWindows]
  | cons A As ih =>
    have hm := hmatch A (List.mem_cons_self ..)
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hapart
    have hmAs : ∀ B ∈ As, B.Matches (A.reverseIn p) := by
      intro B hB
      exact FillingWindow.matches_after_apart A B p (hA B hB)
        (hmatch B (List.mem_cons_of_mem _ hB))
    have htail := ih (A.reverseIn p) hmAs hAs
    have hstep := replace_inversion_price A.window p A.filling Fin.revPerm hm
    rw [inversion_number_reversal] at hstep
    have hstep' : (inversionNumber (A.reverseIn p) : ℤ)+(inversionNumber A.filling : ℤ) =
        (inversionNumber p : ℤ)+(A.size.choose 2 : ℤ) := by exact_mod_cast hstep
    simp only [reverseWindows,List.map_cons,List.sum_cons]
    rw [show A.deficit = (A.size.choose 2 : ℤ)-(inversionNumber A.filling : ℤ) from rfl]
    omega
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Retain individual component sizes in the inversion incidence count. -/
theorem inversion_budget_of_component_sizes (p : State n) :
    2*(inversionNumber p : ℤ) ≤ ∑ i : Fin n, (((componentSet p i).card : ℤ)-1) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => inversion_incidence_le_component p i)
  simp only [Finset.sum_add_distrib] at h
  have he : (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p j i) =
      (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p i j) := Finset.sum_comm
  rw [he,sum_inversion_indicator] at h
  simpa only [← two_mul] using h

/-- All selected filling deficits fit within the capacities of the original
components. This holds for arbitrary canonical finite permutations. -/
theorem source_reversal_component_capacity (p : State n) (L : ℕ) :
    2*((inversionNumber p : ℤ)+((positiveSourceFamily p L).map FillingWindow.deficit).sum) ≤
      ∑ i : Fin n, (((componentSet p i).card : ℤ)-1) := by
  let R := reverseWindows (positiveSourceFamily p L) p.symm
  obtain ⟨hm,hd,_,_⟩ := positive_source_family_spec p L
  have hprice := reverse_windows_inversion_price (positiveSourceFamily p L) p.symm hm hd
  have hi : inversionNumber p.symm = inversionNumber p := inversion_number_inverse p
  rw [hi] at hprice
  have hcap := inversion_budget_of_component_sizes R.symm
  have hiR : inversionNumber R.symm = inversionNumber R := inversion_number_inverse R
  rw [hiR] at hcap
  have hc (i : Fin n) : componentSet R.symm i = componentSet p i := by
    change CycleFootprint.component (displacement R) i = componentSet p i
    exact source_reversal_component_eq p L i
  simp_rw [hc] at hcap
  change (inversionNumber R : ℤ) = _ at hprice
  rw [hprice] at hcap
  exact hcap

/-- The exterior filling reserve pays its internal deficits plus the
cross-component capacity loss, without an assumed majorization. -/
theorem source_gap_deficit_component_reserve (p : State n) (L : ℕ) :
    2*((n.choose 2 : ℤ)-(inversionNumber p : ℤ)-
        ((positiveSourceFamily p L).map FillingWindow.deficit).sum) ≥
      2*(n.choose 2 : ℤ) - ∑ i : Fin n, (((componentSet p i).card : ℤ)-1) := by
  have h := source_reversal_component_capacity p L
  linarith

#print axioms inversion_budget_of_component_sizes
#print axioms source_reversal_component_capacity
#print axioms source_gap_deficit_component_reserve
end LRX.FiniteCuts
