import LRX.ContractionStructure

namespace LRX.ContractionBlocks
variable {m k : ℕ}

def mergeLists (blocks : Fin (k+1) → List (Fin m)) (a b : Fin (k+1)) (i : Fin k) : List (Fin m) :=
  if a.succAbove i=b then blocks a++blocks b else blocks (a.succAbove i)

theorem merge_nonempty (blocks : Fin (k+1) → List (Fin m))
    (hne : ∀ i, blocks i ≠ []) (a b : Fin (k+1)) (i : Fin k) : mergeLists blocks a b i ≠ [] := by
  unfold mergeLists
  split_ifs <;> simp [hne]

theorem merge_membership (blocks : Fin (k+1) → List (Fin m)) (a b : Fin (k+1))
    (i : Fin k) (x : Fin m) :
    x ∈ mergeLists blocks a b i ↔ ∃ s : Fin (k+1),
      (s=a.succAbove i ∨ (s=a ∧ a.succAbove i=b)) ∧ x ∈ blocks s := by
  by_cases hi : a.succAbove i=b
  · simp only [mergeLists,if_pos hi,List.mem_append]
    constructor
    · intro h
      rcases h with h | h
      · exact ⟨a,Or.inr ⟨rfl,hi⟩,h⟩
      · exact ⟨b,Or.inl hi.symm,h⟩
    · rintro ⟨s,hs,hx⟩
      rcases hs with hs | ⟨rfl,_⟩
      · exact Or.inr (hs.trans hi ▸ hx)
      · exact Or.inl hx
  · simp only [mergeLists,if_neg hi]
    constructor
    · intro h
      exact ⟨a.succAbove i,Or.inl rfl,h⟩
    · rintro ⟨s,hs,hx⟩
      rcases hs with rfl | ⟨_,he⟩
      · exact hx
      · exact False.elim (hi he)

theorem contributor_order (a b : Fin (k+1)) (hadj : |(b : ℤ)-(a : ℤ)|=1)
    (i j : Fin k) (hij : i.val < j.val) (s t : Fin (k+1))
    (hs : s=a.succAbove i ∨ (s=a ∧ a.succAbove i=b))
    (ht : t=a.succAbove j ∨ (t=a ∧ a.succAbove j=b)) : s.val < t.val := by
  have hlt : (a.succAbove i).val < (a.succAbove j).val :=
    Fin.succAbove_lt_succAbove_iff.mpr hij
  have hni : (a.succAbove i).val ≠ a.val := fun h => a.succAbove_ne i (Fin.ext h)
  have hnj : (a.succAbove j).val ≠ a.val := fun h => a.succAbove_ne j (Fin.ext h)
  simp only [abs_eq_max_neg] at hadj
  rcases hs with rfl | ⟨rfl,hi⟩ <;> rcases ht with rfl | ⟨rfl,hj⟩
  · exact hlt
  · have hv := congrArg Fin.val hj; omega
  · have hv := congrArg Fin.val hi; omega
  · have hvi := congrArg Fin.val hi; have hvj := congrArg Fin.val hj; omega

theorem merged_last (blocks : Fin (k+1) → List (Fin m)) (hne : ∀ i, blocks i ≠ [])
    (a b : Fin (k+1)) (i : Fin k) :
    (mergeLists blocks a b i).getLast (merge_nonempty blocks hne a b i)=
      (blocks (a.succAbove i)).getLast (hne _) := by
  by_cases hi : a.succAbove i=b
  · simp only [mergeLists,if_pos hi]
    rw [List.getLast_append_of_right_ne_nil _ _ (hne b)]
    simp only [hi]
  · simp only [mergeLists,if_neg hi]

theorem merged_head (blocks : Fin (k+1) → List (Fin m)) (hne : ∀ i, blocks i ≠ [])
    (a b : Fin (k+1)) (hadj : |(b : ℤ)-(a : ℤ)|=1) (i : Fin k) :
    (mergeLists blocks a b i).head (merge_nonempty blocks hne a b i)=
      (blocks (b.succAbove i)).head (hne _) := by
  have hs := FiniteCuts.adjacent_complement_swap a b hadj i
  by_cases hi : a.succAbove i=b
  · have hb : b.succAbove i=a := by
      apply (Equiv.swap a b).injective
      rw [← hs,hi,Equiv.swap_apply_left]
    simp only [mergeLists,if_pos hi,hb]
    exact List.head_append_of_ne_nil (hne a)
  · have hba : b.succAbove i ≠ a := by intro h; rw [h,Equiv.swap_apply_left] at hs; exact hi hs
    rw [Equiv.swap_apply_of_ne_of_ne hba (b.succAbove_ne i)] at hs
    simp only [mergeLists,if_neg hi]
    simp only [hs]

#print axioms contributor_order
#print axioms merged_head
#print axioms merged_last
end LRX.ContractionBlocks
