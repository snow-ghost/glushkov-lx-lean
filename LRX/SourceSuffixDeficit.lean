import LRX.SuffixFamilyComponentCapacity

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow
variable {n b : ℕ} [NeZero n] [NeZero b]

/-- The already extracted original source gaps lying in the suffix. -/
noncomputable def suffixSourceFamily (p : State n) (offset : ℕ) : List (FillingWindow n) :=
  (positiveSourceFamily p n).filter (fun A => decide (offset ≤ A.window.offset))

/-- The suffix's actual inversion count and the original outside gap deficits
fit within the sizes of the original ambient components. -/
theorem source_suffix_component_capacity (p : State n) (W : Window n b)
    (hend : W.offset+b = n) (f : State b)
    (hmatch : ∀ i, p.symm (embed W i) = embed W (f i)) :
    2*((inversionNumber f : ℤ)+((suffixSourceFamily p W.offset).map FillingWindow.deficit).sum) ≤
      ∑ i : Fin b, (((componentSet p (embed W i)).card : ℤ)-1) := by
  obtain ⟨hm,hd,_,_⟩ := positive_source_family_spec p n
  apply suffix_family_component_capacity W hend p.symm f hmatch (suffixSourceFamily p W.offset)
  · intro A hA
    exact hm A (List.mem_filter.mp hA).1
  · exact hd.filter _
  · intro A hA
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hA).2
  · intro A hA r hr hr'
    exact positive_source_family_internal_ports p n A (List.mem_filter.mp hA).1 r hr hr'

/-- External deficit pays original external internal-gap deficits plus the
cross-component reserve, with no assumed identification of source packets. -/
theorem source_suffix_deficit_reserve (p : State n) (W : Window n b)
    (hend : W.offset+b = n) (f : State b)
    (hmatch : ∀ i, p.symm (embed W i) = embed W (f i)) :
    2*((b.choose 2 : ℤ)-(inversionNumber f : ℤ)) ≥
      2*((suffixSourceFamily p W.offset).map FillingWindow.deficit).sum +
      2*(b.choose 2 : ℤ) - ∑ i : Fin b, (((componentSet p (embed W i)).card : ℤ)-1) := by
  have h := source_suffix_component_capacity p W hend f hmatch
  linarith

#print axioms source_suffix_component_capacity
#print axioms source_suffix_deficit_reserve
end LRX.FiniteCuts
