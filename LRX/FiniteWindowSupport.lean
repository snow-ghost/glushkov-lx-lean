import LRX.FiniteWindow
import Mathlib

namespace LRX.FiniteWindow
variable {n b : ℕ}

theorem permutation_support (W : Window n b) (p : State b) :
    (permutation W p).support=p.support.image (embed W) := by
  classical
  ext j
  constructor
  · intro hj
    have hcontains : Contains W j := by
      by_contra hout
      exact (Equiv.Perm.mem_support.mp hj) (permutation_outside W p j hout)
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp hcontains
    apply Finset.mem_image.mpr
    refine ⟨i,?_,rfl⟩
    apply Equiv.Perm.mem_support.mpr
    intro hi
    apply (Equiv.Perm.mem_support.mp hj)
    rw [permutation_embed,hi]
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    apply Equiv.Perm.mem_support.mpr
    rw [permutation_embed]
    intro h
    exact (Equiv.Perm.mem_support.mp hi) (embed_injective W h)

theorem permutation_support_card (W : Window n b) (p : State b) :
    (permutation W p).support.card=p.support.card := by
  rw [permutation_support,Finset.card_image_of_injective _ (embed_injective W)]


#print axioms permutation_support_card
end LRX.FiniteWindow
