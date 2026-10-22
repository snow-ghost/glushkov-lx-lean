import LRX.PrunedLoad

/-! The complement of the selected factor's support is the retained root
factor, when the two physical target permutations are disjoint. -/
namespace LRX.PrunedLift
variable {n : ℕ}

theorem selected_complement_invariant (root selected : State n) (hd : root.Disjoint selected)
    (i : Fin n) : (root*selected) i ∈ selected.supportᶜ ↔ i ∈ selected.supportᶜ := by
  have hc : selected*(root*selected)=(root*selected)*selected := by
    rw [← mul_assoc, ← hd.commute.eq]
  have hi := congrArg (fun p : State n => p i) hc
  simp only [Equiv.Perm.mul_apply] at hi
  simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
  change selected ((root*selected) i)=(root*selected) i ↔ selected i=i
  have he : selected ((root*selected) i)=(root*selected) (selected i) := hi
  rw [he]
  exact (root*selected).injective.eq_iff

theorem retained_factor (root selected : State n) (hd : root.Disjoint selected) :
    permutation (root*selected) selected.supportᶜ
      (selected_complement_invariant root selected hd)=root := by
  apply Equiv.ext
  intro i
  by_cases hi : selected i=i
  · simp [Equiv.Perm.mul_apply, hi]
  · have hr : root i=i := (hd i).resolve_right hi
    simp [Equiv.Perm.mem_support, hi, hr]

theorem retained_displacement (root selected : State n) (hd : root.Disjoint selected) :
    displacement selected.supportᶜ (fun i => ((root*selected).symm i : ℤ)-(i : ℤ))=
      (fun i => (root.symm i : ℤ)-(i : ℤ)) := by
  funext i
  by_cases hi : selected i=i
  · have him : i ∈ selected.supportᶜ := by simpa using hi
    have he := congrArg (fun p : State n => p.symm i) (retained_factor root selected hd)
    rw [permutation_symm_apply, ite_eq_left him] at he
    simp only [displacement, ite_eq_left him, he]
  · have hr : root i=i := (hd i).resolve_right hi
    have hri : root.symm i=i := by apply root.injective; simpa using hr.symm
    simp [displacement, Equiv.Perm.mem_support, hi, hri]

theorem keep_root_zero [NeZero n] (root selected : State n)
    (hd : root.Disjoint selected) (hroot : root 0 ≠ 0) :
    (0 : Fin n) ∈ selected.supportᶜ := by
  simpa using (hd 0).resolve_left hroot

#print axioms retained_factor
#print axioms retained_displacement
end LRX.PrunedLift
