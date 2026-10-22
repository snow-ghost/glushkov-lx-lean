import LRX.PrunedPartition

/-! A selected union of cycles agrees with the original permutation on its
support. Its complement is invariant and composes back to the full target. -/
namespace LRX.CyclePart
variable {n : ℕ}

def IsPart (selected full : State n) : Prop := ∀ i, selected i ≠ i → selected i=full i

theorem support_invariant (selected full : State n) (h : IsPart selected full) (i : Fin n) :
    full i ∈ selected.support ↔ i ∈ selected.support := by
  have hs : selected.support.image full ⊆ selected.support := by
    intro j hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
    rw [← h a (Equiv.Perm.mem_support.mp ha)]
    exact selected.apply_mem_support.mpr ha
  have he : selected.support.image full=selected.support := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [Finset.card_image_of_injective _ full.injective]
  constructor
  · intro hi
    rw [← he] at hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
    have := full.injective hji
    simpa only [this] using hj
  · intro hi
    rw [← he]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩

theorem selected_restriction (selected full : State n) (h : IsPart selected full) :
    PrunedLift.permutation full selected.support (support_invariant selected full h)=selected := by
  apply Equiv.ext
  intro i
  by_cases hi : selected i=i
  · simp [hi]
  · simp only [PrunedLift.permutation_apply,Equiv.Perm.mem_support,ite_eq_left hi]
    exact (h i hi).symm

theorem inverse_on_support (selected full : State n) (h : IsPart selected full)
    (i : Fin n) (hi : i ∈ selected.support) : full.symm i=selected.symm i := by
  have he := congrArg (fun p : State n => p.symm i) (selected_restriction selected full h)
  simpa only [PrunedLift.permutation_symm_apply,ite_eq_left hi] using he

def remaining (selected full : State n) (h : IsPart selected full) : State n :=
  PrunedLift.permutation full selected.supportᶜ
    (PrunedLift.complement_invariant full selected.support (support_invariant selected full h))

theorem remaining_disjoint (selected full : State n) (h : IsPart selected full) :
    (remaining selected full h).Disjoint selected := by
  have hd := PrunedLift.permutation_disjoint full selected.support (support_invariant selected full h)
  rw [selected_restriction selected full h] at hd
  exact hd.symm

theorem remaining_product (selected full : State n) (h : IsPart selected full) :
    remaining selected full h*selected=full := by
  have hp := PrunedLift.permutation_partition full selected.support (support_invariant selected full h)
  rw [selected_restriction selected full h] at hp
  rw [(remaining_disjoint selected full h).commute.eq]
  exact hp

#print axioms inverse_on_support
#print axioms remaining_product
end LRX.CyclePart
