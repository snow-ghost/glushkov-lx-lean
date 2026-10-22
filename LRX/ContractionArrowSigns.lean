import LRX.ContractionBlockGeometry

namespace LRX.ContractionBlocks.System
variable {m k : ℕ} {P : State m} {q : State k}

def positive (B : System P q) : Finset (Fin m) :=
  B.selected.filter (fun x => x.val < (P x).val)

def negative (B : System P q) : Finset (Fin m) :=
  B.selected.filter (fun x => (P x).val < x.val)

theorem signs_partition (B : System P q) :
    B.positive ∪ B.negative = B.selected := by
  ext x
  simp only [positive, negative, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hx
    have hne : (P x).val ≠ x.val := fun h => B.selected_source_moved x hx (Fin.ext h)
    by_cases h : x.val < (P x).val
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨hx,by omega⟩

theorem signs_disjoint (B : System P q) : Disjoint B.positive B.negative := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hp := (Finset.mem_filter.mp hx).2
  have hn := (Finset.mem_filter.mp hy).2
  omega

theorem signs_card (B : System P q) : B.positive.card+B.negative.card+k=m := by
  have h := Finset.card_union_of_disjoint B.signs_disjoint
  rw [B.signs_partition] at h
  have hc := B.selected_card
  omega

theorem positive_contract {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) (hne : q a ≠ a) :
    (B.contract a hadj).positive =
      if a.val < (q a).val then insert (B.lastLabel a) B.positive else B.positive := by
  unfold positive
  rw [selected_contract, Finset.filter_insert]
  simp only [B.selected_arrow_positive_iff a hne]

theorem positive_contract_card {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) (hne : q a ≠ a) :
    (B.contract a hadj).positive.card =
      B.positive.card + if a.val < (q a).val then 1 else 0 := by
  rw [positive_contract B a hadj hne]
  have hn : B.lastLabel a ∉ B.positive := fun h =>
    B.last_not_selected a (Finset.mem_filter.mp h).1
  split_ifs <;> simp [Finset.card_insert_of_notMem hn]

theorem negative_contract_card {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) (hne : q a ≠ a) :
    (B.contract a hadj).negative.card =
      B.negative.card + if (q a).val < a.val then 1 else 0 := by
  have ho := B.signs_card
  have hn := (B.contract a hadj).signs_card
  have hp := B.positive_contract_card a hadj hne
  have hne' : (q a).val ≠ a.val := fun h => hne (Fin.ext h)
  split_ifs at hp ⊢ <;> omega

#print axioms signs_card
#print axioms positive_contract_card
#print axioms negative_contract_card
end LRX.ContractionBlocks.System
