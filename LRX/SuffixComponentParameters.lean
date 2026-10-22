import LRX.SuffixComponentPartition
import LRX.ComponentCrossMinimum

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def nontrivialSuffixComponents (p : State n) (L : ℕ) :=
  (suffixComponents p L).filter (fun C => 2 ≤ C.card)

noncomputable def singletonSuffixComponents (p : State n) (L : ℕ) :=
  (suffixComponents p L).filter (fun C => C.card = 1)

theorem suffix_component_nonempty (p : State n) (L : ℕ) (C : Finset (Fin n))
    (hC : C ∈ suffixComponents p L) : 0 < C.card := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
  exact Finset.card_pos.mpr ⟨i,(CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl⟩

theorem suffix_vertices_card (L : ℕ) (hLn : L ≤ n) : (suffixVertices n L).card = n-L := by
  rw [suffix_vertices_image L hLn,Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp at h
    omega

/-- The actual exterior size is the sum of nontrivial sizes and singleton count. -/
theorem suffix_component_parameter_sum (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    (∑ C ∈ nontrivialSuffixComponents p L, C.card) + (singletonSuffixComponents p L).card = n-L := by
  classical
  have htotal := CycleFootprint.component_blocks_card_sum (displacement p.symm)
    (suffixVertices n L) (invariant_suffix_closed p L hLn hcut)
  rw [suffix_vertices_card L hLn] at htotal
  have hones : (∑ C ∈ suffixComponents p L, if C.card = 1 then (1 : ℕ) else 0) =
      (singletonSuffixComponents p L).card := by
    rw [← Finset.sum_filter]
    simp [singletonSuffixComponents]
  rw [← hones]
  unfold nontrivialSuffixComponents
  rw [Finset.sum_filter,← Finset.sum_add_distrib]
  calc
    _ = ∑ C ∈ suffixComponents p L, C.card := by
      apply Finset.sum_congr rfl
      intro C hC
      have hc := suffix_component_nonempty p L C hC
      split_ifs <;> omega
    _ = _ := htotal

theorem nontrivial_suffix_size_sum (p : State n) (L : ℕ) :
    2*(nontrivialSuffixComponents p L).card ≤ ∑ C ∈ nontrivialSuffixComponents p L, C.card := by
  classical
  calc
    _ = ∑ _C ∈ nontrivialSuffixComponents p L, (2 : ℕ) := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun C hC => (Finset.mem_filter.mp hC).2)

theorem suffix_choose_sum_nontrivial (p : State n) (L : ℕ) :
    (∑ C ∈ suffixComponents p L, (C.card.choose 2 : ℤ)) =
      ∑ C ∈ nontrivialSuffixComponents p L, (C.card.choose 2 : ℤ) := by
  classical
  unfold nontrivialSuffixComponents
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h : 2 ≤ C.card
  · simp [h]
  · have hz : C.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h,hz]

/-- C7's numeric cross lower bound, with every size and count extracted from
actual exterior components. Singleton positions are counted as components. -/
theorem suffix_cross_numeric_lower (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    let t := (nontrivialSuffixComponents p L).card
    let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
    let a := (singletonSuffixComponents p L).card
    2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤
      ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents p L, (C.card.choose 2 : ℤ)) := by
  classical
  have h := component_cross_minimum_with_isolated (nontrivialSuffixComponents p L)
    Finset.card (fun C hC => (Finset.mem_filter.mp hC).2) (singletonSuffixComponents p L).card
  dsimp only at h ⊢
  rw [suffix_component_parameter_sum p L hLn hcut] at h
  rw [suffix_choose_sum_nontrivial p L]
  exact h

#print axioms suffix_component_parameter_sum
#print axioms suffix_cross_numeric_lower
end LRX.FiniteCuts
