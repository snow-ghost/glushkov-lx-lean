import LRX.ContractionSelectedCapacity

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

/-- The boundary of all selected paths consists exactly of their first and
last labels; the remaining permutation rearranges the first labels. -/
theorem selected_flux (B : System P q) (f : Fin m → ℤ) :
    (∑ x ∈ B.selected, (f (P x)-f x)) = ∑ i, (f (B.lastLabel i)-f (B.firstLabel i)) := by
  have hzero : (∑ x : Fin m, (f (P x)-f x))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp P f,sub_self]
  have hsplit := Finset.sum_sdiff_eq_sub (s₁ := Finset.univ.image B.lastLabel)
    (s₂ := Finset.univ) (f := fun x => f (P x)-f x) (Finset.subset_univ _)
  change (∑ x ∈ B.selected, (f (P x)-f x)) = _ at hsplit
  rw [hzero,Finset.sum_image (fun x _ y _ h => B.last_injective h)] at hsplit
  have he : ∀ i, P (B.lastLabel i)=B.firstLabel (q i) := B.edge
  simp only [he,Finset.sum_sub_distrib] at hsplit ⊢
  rw [Equiv.sum_comp q (fun i => f (B.firstLabel i))] at hsplit
  omega

def rightOf (gap : ℕ) (x : Fin m) : ℤ := if gap < x.val then 1 else 0

/-- Distinct ordered blocks cannot both straddle one cut. -/
theorem boundary_diff_unique (B : System P q) (gap : ℕ) (i j : Fin k)
    (hi : rightOf gap (B.lastLabel i)-rightOf gap (B.firstLabel i) ≠ 0)
    (hj : rightOf gap (B.lastLabel j)-rightOf gap (B.firstLabel j) ≠ 0) : i=j := by
  have hli := List.getLast_mem (B.nonempty i)
  have hfi := List.head_mem (B.nonempty i)
  have hlj := List.getLast_mem (B.nonempty j)
  have hfj := List.head_mem (B.nonempty j)
  by_contra hne
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · have hll := B.ordered i j hij _ hli _ hlj
    have hlf := B.ordered i j hij _ hli _ hfj
    have hfl := B.ordered i j hij _ hfi _ hlj
    have hff := B.ordered i j hij _ hfi _ hfj
    simp only [rightOf,firstLabel,lastLabel] at hi hj
    split_ifs at hi hj <;> omega
  · have hll := B.ordered j i (by omega) _ hlj _ hli
    have hlf := B.ordered j i (by omega) _ hlj _ hfi
    have hfl := B.ordered j i (by omega) _ hfj _ hli
    have hff := B.ordered j i (by omega) _ hfj _ hfi
    simp only [rightOf,firstLabel,lastLabel] at hi hj
    split_ifs at hi hj <;> omega

theorem selected_cut_flux_bound (B : System P q) (gap : ℕ) :
    |∑ x ∈ B.selected, (rightOf gap (P x)-rightOf gap x)| ≤ 1 := by
  rw [B.selected_flux]
  by_cases he : ∃ i, rightOf gap (B.lastLabel i)-rightOf gap (B.firstLabel i) ≠ 0
  · obtain ⟨i,hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp only [rightOf]
      split_ifs <;> norm_num
    · intro j _ hji
      by_contra hj
      exact hji (B.boundary_diff_unique gap j i hj hi)
    · simp
  · have hz : ∀ i, rightOf gap (B.lastLabel i)-rightOf gap (B.firstLabel i)=0 := by
      simpa using he
    simp [hz]

#print axioms selected_flux
#print axioms selected_cut_flux_bound
end LRX.ContractionBlocks.System
