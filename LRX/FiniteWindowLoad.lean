import LRX.FiniteWindow

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

theorem forward_window (W : Window n b) (p : State b) (e : ℕ) :
    FiniteCuts.forward (permutation W p) (W.offset+e)=
      (FiniteCuts.forward p e).image (embed W) := by
  ext j
  constructor
  · intro hj
    obtain ⟨hl,hr⟩ := (FiniteCuts.mem_forward _ _ _).mp hj
    have hm : Contains W j := by
      by_contra h
      rw [permutation_outside W p j h] at hr
      omega
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp hm
    refine Finset.mem_image.mpr ⟨i,?_,rfl⟩
    rw [FiniteCuts.mem_forward]
    rw [permutation_embed] at hr
    dsimp [embed] at hl hr
    omega
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hl,hr⟩ := (FiniteCuts.mem_forward _ _ _).mp hi
    rw [FiniteCuts.mem_forward,permutation_embed]
    dsimp [embed]
    omega

theorem half_load_window (W : Window n b) (p : State b) (e : ℕ) :
    FiniteCuts.halfLoad (permutation W p) (W.offset+e)=FiniteCuts.halfLoad p e := by
  unfold FiniteCuts.halfLoad
  rw [forward_window,Finset.card_image_of_injective _ (embed_injective W)]

#print axioms displacement_mass
#print axioms half_load_window
end LRX.FiniteWindow
