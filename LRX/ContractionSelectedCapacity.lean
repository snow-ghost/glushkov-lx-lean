import LRX.ContractionBlockCapacity

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

def within (B : System P q) (S : Finset (Fin m)) (i : Fin k) := S ∩ B.labels i

theorem within_disjoint (B : System P q) (S : Finset (Fin m)) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) (B.within S) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact B.nodes_distinct i j hij
    (List.mem_toFinset.mp (Finset.mem_inter.mp hx).2)
    (List.mem_toFinset.mp (Finset.mem_inter.mp hy).2) rfl

theorem within_union (B : System P q) (S : Finset (Fin m)) :
    Finset.univ.biUnion (B.within S)=S := by
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,within,Finset.mem_inter]
  constructor
  · rintro ⟨i,hx,_⟩; exact hx
  · intro hx
    obtain ⟨i,hi⟩ := B.cover x
    exact ⟨i,hx,List.mem_toFinset.mpr hi⟩

theorem sum_within {β : Type*} [AddCommMonoid β] (B : System P q)
    (S : Finset (Fin m)) (f : Fin m → β) :
    (∑ x ∈ S, f x)=∑ i, ∑ x ∈ B.within S i, f x := by
  have h := Finset.sum_biUnion (f:=f) (B.within_disjoint S)
  rwa [B.within_union S] at h

theorem card_within (B : System P q) (S : Finset (Fin m)) :
    ∑ i, (B.within S i).card=S.card := by
  simpa using (B.sum_within S (fun _ => (1 : ℕ))).symm

/-- All labels of a block except its last label are already selected sources.
This controls the unused capacity in each block by the global remainder. -/
theorem block_remainder_bound (B : System P q) (S : Finset (Fin m)) (i : Fin k) :
    (B.labels i).card ≤ (B.within S i).card+(B.selected \ S).card+1 := by
  have hsub : B.labels i ⊆ insert (B.lastLabel i) (B.within S i ∪ (B.selected \ S)) := by
    intro x hx
    by_cases hl : x=B.lastLabel i
    · exact Finset.mem_insert.mpr (Or.inl hl)
    apply Finset.mem_insert_of_mem
    by_cases hs : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hs,hx⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨(B.selected_iff_internal x).mpr
        ⟨i,List.mem_toFinset.mp hx,hl⟩,hs⟩
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_insert_le (B.lastLabel i) (B.within S i ∪ (B.selected \ S))
  have hu := Finset.card_union_le (B.within S i) (B.selected \ S)
  omega

theorem selected_difference_capacity (B : System P q) (S : Finset (Fin m))
    (hS : S ⊆ B.selected) :
    (∑ x ∈ S, ((P x : ℤ)-(x : ℤ))) ≤
      (S.card : ℤ)*((B.selected \ S).card+1) := by
  rw [B.sum_within S]
  calc
    _ ≤ ∑ i, ((B.within S i).card : ℤ)*((B.selected \ S).card+1) := by
      apply Finset.sum_le_sum
      intro i _
      have hcap := B.block_difference_capacity i (B.within S i)
        (fun x hx => hS (Finset.mem_inter.mp hx).1) (fun x hx => (Finset.mem_inter.mp hx).2)
      have hrem := B.block_remainder_bound S i
      have hrem' : ((B.labels i).card : ℤ) ≤
          (B.within S i).card+(B.selected \ S).card+1 := by exact_mod_cast hrem
      have hnon : (0 : ℤ) ≤ (B.within S i).card := by positivity
      nlinarith
    _ = _ := by
      rw [← Finset.sum_mul]
      have hc : (∑ i, ((B.within S i).card : ℤ))=(S.card : ℤ) := by
        exact_mod_cast B.card_within S
      rw [hc]

theorem selected_reverse_difference_capacity (B : System P q) (S : Finset (Fin m))
    (hS : S ⊆ B.selected) :
    (∑ x ∈ S, ((x : ℤ)-(P x : ℤ))) ≤
      (S.card : ℤ)*((B.selected \ S).card+1) := by
  rw [B.sum_within S]
  calc
    _ ≤ ∑ i, ((B.within S i).card : ℤ)*((B.selected \ S).card+1) := by
      apply Finset.sum_le_sum
      intro i _
      have hcap := B.block_reverse_difference_capacity i (B.within S i)
        (fun x hx => hS (Finset.mem_inter.mp hx).1) (fun x hx => (Finset.mem_inter.mp hx).2)
      have hrem := B.block_remainder_bound S i
      have hrem' : ((B.labels i).card : ℤ) ≤
          (B.within S i).card+(B.selected \ S).card+1 := by exact_mod_cast hrem
      have hnon : (0 : ℤ) ≤ (B.within S i).card := by positivity
      nlinarith
    _ = _ := by
      rw [← Finset.sum_mul]
      have hc : (∑ i, ((B.within S i).card : ℤ))=(S.card : ℤ) := by
        exact_mod_cast B.card_within S
      rw [hc]

#print axioms selected_difference_capacity
#print axioms selected_reverse_difference_capacity
end LRX.ContractionBlocks.System
