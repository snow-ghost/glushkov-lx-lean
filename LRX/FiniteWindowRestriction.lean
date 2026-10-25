import LRX.FiniteWindow
import Mathlib

/-! Extract the finite permutation of an invariant physical window. -/
namespace LRX.FiniteWindow
variable {n b : ℕ}

theorem invariant_of_inverse_closed (p : State n) (S : Finset (Fin n))
    (hclosed : ∀ i ∈ S, p.symm i ∈ S) : ∀ i, p i ∈ S ↔ i ∈ S := by
  classical
  have himage : S.image p.symm=S := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr hclosed) (by rw [Finset.card_image_of_injective _ p.symm.injective])
  intro i
  constructor
  · intro hi
    simpa using hclosed (p i) hi
  · intro hi
    rw [← himage] at hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    simpa only [← he,p.apply_symm_apply] using hj

def restriction (W : Window n b) (p : State n) (hW : ∀ j, Contains W (p j) ↔ Contains W j) : State b :=
  ((windowEquiv W).trans (p.subtypePerm hW)).trans (windowEquiv W).symm

theorem embed_restriction (W : Window n b) (p : State n)
    (hW : ∀ j, Contains W (p j) ↔ Contains W j) (i : Fin b) :
    embed W (restriction W p hW i)=p (embed W i) := by
  change ((windowEquiv W) ((windowEquiv W).symm ((p.subtypePerm hW) ((windowEquiv W) i)))).val= _
  rw [Equiv.apply_symm_apply]
  rfl

theorem exists_restriction_of_inverse_closed (W : Window n b) (p : State n)
    (hclosed : ∀ j, Contains W j → Contains W (p.symm j)) :
    ∃ filling : State b, ∀ i, p.symm (embed W i)=embed W (filling i) := by
  classical
  let S := Finset.univ.filter (Contains W)
  have hS : ∀ j, p j ∈ S ↔ j ∈ S := invariant_of_inverse_closed p S
    (fun j hj => by simpa [S] using hclosed j (by simpa [S] using hj))
  have hW : ∀ j, Contains W (p.symm j) ↔ Contains W j := by
    intro j
    have h := hS (p.symm j)
    simpa [S] using h.symm
  exact ⟨restriction W p.symm hW,fun i => (embed_restriction W p.symm hW i).symm⟩

#print axioms exists_restriction_of_inverse_closed
end LRX.FiniteWindow
