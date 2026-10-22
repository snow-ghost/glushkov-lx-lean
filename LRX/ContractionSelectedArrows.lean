import LRX.ContractionPathSystem

namespace LRX.ContractionBlocks.System
variable {m k : ℕ} {P : State m} {q : State k}

def firstLabel (B : System P q) (i : Fin k) : Fin m := (B.nodes i).head (B.nonempty i)
def lastLabel (B : System P q) (i : Fin k) : Fin m := (B.nodes i).getLast (B.nonempty i)

def selected (B : System P q) : Finset (Fin m) := Finset.univ \ Finset.univ.image B.lastLabel

@[simp] theorem mem_selected (B : System P q) (x : Fin m) :
    x ∈ B.selected ↔ ∀ i, x ≠ B.lastLabel i := by
  simp [selected,eq_comm]

theorem last_injective (B : System P q) : Function.Injective B.lastLabel := by
  intro i j h
  by_contra hij
  exact B.nodes_distinct i j hij (List.getLast_mem (B.nonempty i)) (List.getLast_mem (B.nonempty j)) h

theorem selected_card (B : System P q) : B.selected.card+k=m := by
  have hle : k ≤ m := by simpa using Fintype.card_le_of_injective B.lastLabel B.last_injective
  unfold selected
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_image_of_injective _ B.last_injective]
  simp only [Finset.card_univ,Fintype.card_fin]
  omega

theorem last_not_selected (B : System P q) (a : Fin k) : B.lastLabel a ∉ B.selected := by
  rw [mem_selected]
  intro h
  exact h a rfl

/-- Selected sources are exactly the nonfinal vertices of the path blocks. -/
theorem selected_iff_internal (B : System P q) (x : Fin m) :
    x ∈ B.selected ↔ ∃ i, x ∈ B.nodes i ∧ x ≠ B.lastLabel i := by
  rw [mem_selected]
  constructor
  · intro h
    obtain ⟨i,hi⟩ := B.cover x
    exact ⟨i,hi,h i⟩
  · rintro ⟨i,hi,hne⟩ j he
    by_cases hij : i=j
    · subst j
      exact hne he
    · exact B.nodes_distinct i j hij hi (List.getLast_mem (B.nonempty j)) he

theorem contract_last {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) (i : Fin k) :
    (B.contract a hadj).lastLabel i=B.lastLabel (a.succAbove i) :=
  merged_last B.nodes B.nonempty a (q a) i

/-- Exactly one new original source is selected, and it was not selected before. -/
theorem selected_contract {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) :
    (B.contract a hadj).selected=insert (B.lastLabel a) B.selected := by
  ext x
  simp only [mem_selected,Finset.mem_insert,contract_last]
  constructor
  · intro h
    by_cases hxa : x=B.lastLabel a
    · exact Or.inl hxa
    · right
      intro j hj
      by_cases hja : j=a
      · subst j; exact hxa hj
      · obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hja
        exact h i (by rwa [hi])
  · intro h i he
    rcases h with h | h
    · have hlabels : B.lastLabel a=B.lastLabel (a.succAbove i) := h.symm.trans he
      exact a.succAbove_ne i (B.last_injective hlabels).symm
    · exact h (a.succAbove i) he

theorem selected_contract_card {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) :
    (B.contract a hadj).selected.card=B.selected.card+1 := by
  rw [selected_contract,Finset.card_insert_of_notMem (B.last_not_selected a)]

/-- Order of the blocks makes the sign of the current arrow equal to the
sign of the actual original arrow added to the selected set. -/
theorem selected_arrow_positive_iff (B : System P q) (a : Fin k) (hne : q a ≠ a) :
    (B.lastLabel a).val < (P (B.lastLabel a)).val ↔ a.val < (q a).val := by
  have he : P (B.lastLabel a)=B.firstLabel (q a) := B.edge a
  rw [he]
  have hx := List.getLast_mem (B.nonempty a)
  have hy := List.head_mem (B.nonempty (q a))
  have hneq : (q a).val ≠ a.val := fun h => hne (Fin.ext h)
  constructor
  · intro h
    by_contra hnot
    have hrev := B.ordered (q a) a (by omega) (B.firstLabel (q a)) hy (B.lastLabel a) hx
    omega
  · intro h
    exact B.ordered a (q a) h (B.lastLabel a) hx (B.firstLabel (q a)) hy

#print axioms selected_card
#print axioms selected_contract
#print axioms selected_arrow_positive_iff
end LRX.ContractionBlocks.System
