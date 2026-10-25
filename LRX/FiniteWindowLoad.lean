import LRX.FiniteWindow
import Mathlib

/-! Exact mass and cut-load identities for an embedded finite window. -/
namespace LRX.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem sum_window (W : Window n b) (f : Fin n → ℤ)
    (hzero : ∀ j, ¬Contains W j → f j=0) :
    (∑ j : Fin n, f j)=∑ i : Fin b, f (embed W i) := by
  classical
  let S := Finset.univ.image (embed W)
  have hsub : (∑ j ∈ S, f j)=∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    apply hzero j
    intro h
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp h
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [← hsub]
  exact Finset.sum_image (fun i _ j _ h => embed_injective W h)

theorem displacement_mass (W : Window n b) (p : State b) :
    (∑ j : Fin n, |FiniteCuts.displacement (permutation W p) j|)=
      ∑ i : Fin b, |FiniteCuts.displacement p i| := by
  rw [sum_window W _ (fun j hj => by rw [displacement_outside W p j hj,abs_zero])]
  simp only [displacement_embed]


#print axioms displacement_mass
end LRX.FiniteWindow
