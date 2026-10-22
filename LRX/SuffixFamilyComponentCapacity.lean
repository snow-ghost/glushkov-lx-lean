import LRX.SuffixWindowPullback
import LRX.ReversalFamilyComponentCapacity

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n] [NeZero b]

/-- Pull the actual windows into the suffix, retaining their exact deficits,
and measure the resulting capacity in original ambient component sizes. -/
theorem suffix_family_component_capacity (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (As : List (FillingWindow n))
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart)
    (hstart : ∀ A ∈ As, W.offset ≤ A.window.offset)
    (hloaded : ∀ A ∈ As, ∀ r : Fin n,
      A.window.offset < r.val+1 → r.val+1 < A.window.offset+A.size →
      0 < portLoad (displacement p) r) :
    2*((inversionNumber f : ℤ)+(As.map FillingWindow.deficit).sum) ≤
      ∑ i : Fin b, (((CycleFootprint.component (displacement p) (embed W i)).card : ℤ)-1) := by
  let Bs := As.pmap (pullSuffixFilling W hend) hstart
  have hmB : ∀ B ∈ Bs, B.Matches f := by
    intro B hB
    obtain ⟨A,hA,rfl⟩ := List.mem_pmap.mp hB
    exact pull_suffix_filling_matches W hend p f hmatch A (hstart A hA) (hm A hA)
  have hdB : Bs.Pairwise FillingWindow.Apart := by
    exact hd.pmap hstart (fun {A} hA {B} hB hAB => pull_suffix_fillings_apart W hend A B hA hB hAB)
  have hlB : ∀ B ∈ Bs, ∀ r : Fin b,
      B.window.offset < r.val+1 → r.val+1 < B.window.offset+B.size →
      0 < portLoad (displacement f) r := by
    intro B hB r hr hr'
    obtain ⟨A,hA,rfl⟩ := List.mem_pmap.mp hB
    exact pull_suffix_internal_load W hend p f hmatch A (hstart A hA) (hloaded A hA) r hr hr'
  have hdef : Bs.map FillingWindow.deficit = As.map FillingWindow.deficit := by
    simp only [Bs,List.map_pmap,pull_suffix_filling_deficit,List.pmap_eq_map]
  have hcap := reversal_family_component_capacity Bs f hmB hdB hlB
  rw [hdef] at hcap
  simp_rw [suffix_component_card W hend p f hmatch] at hcap
  exact hcap

#print axioms suffix_family_component_capacity
end LRX.FiniteWindow
