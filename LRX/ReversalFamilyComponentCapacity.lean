import LRX.SourceReversalComponentCapacity

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Component capacity for any actual internally loaded disjoint window family. -/
theorem reversal_family_component_capacity (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p) (hapart : As.Pairwise FillingWindow.Apart)
    (hloaded : ∀ A ∈ As, ∀ r : Fin n,
      A.window.offset < r.val+1 → r.val+1 < A.window.offset+A.size →
      0 < RotationWords.portLoad (displacement p) r) :
    2*((inversionNumber p : ℤ)+(As.map FillingWindow.deficit).sum) ≤
      ∑ i : Fin n, (((CycleFootprint.component (displacement p) i).card : ℤ)-1) := by
  let R := reverseWindows As p
  have hports := reverse_windows_positive_port_iff As p hmatch hapart hloaded
  have hc (i : Fin n) : componentSet R.symm i = CycleFootprint.component (displacement p) i := by
    ext j
    change j ∈ CycleFootprint.component (displacement R) i ↔ _
    simp only [CycleFootprint.mem_component]
    exact load_path_iff_of_positive_ports _ _ hports i j
  have hcap := inversion_budget_of_component_sizes R.symm
  have hiR : inversionNumber R.symm = inversionNumber R := inversion_number_inverse R
  rw [hiR] at hcap
  simp_rw [hc] at hcap
  have hprice := reverse_windows_inversion_price As p hmatch hapart
  change (inversionNumber R : ℤ) = _ at hprice
  rw [hprice] at hcap
  exact hcap

#print axioms reversal_family_component_capacity
end LRX.FiniteWindow
