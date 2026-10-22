import LRX.LoadComponentSet
import LRX.GapCostInversionDeficit

namespace LRX.CycleFootprint
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem component_eq_of_path (d : Fin n → ℤ) {a b : Fin n} (hp : LoadPath d a b) :
    component d a = component d b := by
  ext i
  simp only [mem_component]
  exact ⟨fun h => (load_path_symm d hp).trans h,fun h => hp.trans h⟩

noncomputable def componentBlocks (d : Fin n → ℤ) (S : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact S.image (component d)

theorem component_blocks_disjoint (d : Fin n → ℤ) (S : Finset (Fin n)) :
    (componentBlocks d S : Set (Finset (Fin n))).PairwiseDisjoint id := by
  classical
  intro A hA B hB hne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hp := ((mem_component d a i).mp hi).trans (load_path_symm d ((mem_component d b i).mp hj))
  exact hne (component_eq_of_path d hp)

theorem component_blocks_union (d : Fin n → ℤ) (S : Finset (Fin n))
    (hclosed : ∀ a ∈ S, ∀ b, LoadPath d a b → b ∈ S) :
    (componentBlocks d S).biUnion id = S := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨A,hA,hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    exact hclosed a ha i ((mem_component d a i).mp hi)
  · intro hi
    apply Finset.mem_biUnion.mpr
    exact ⟨component d i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,(mem_component d i i).mpr Relation.ReflTransGen.refl⟩

theorem component_blocks_card_sum (d : Fin n → ℤ) (S : Finset (Fin n))
    (hclosed : ∀ a ∈ S, ∀ b, LoadPath d a b → b ∈ S) :
    (∑ A ∈ componentBlocks d S, A.card) = S.card := by
  have h := Finset.card_biUnion (component_blocks_disjoint d S)
  rw [component_blocks_union d S hclosed] at h
  exact h.symm

/-- Each component of size k contributes k(k-1), exactly twice choose(k,2). -/
theorem component_blocks_capacity_sum (d : Fin n → ℤ) (S : Finset (Fin n))
    (hclosed : ∀ a ∈ S, ∀ b, LoadPath d a b → b ∈ S) :
    (∑ i ∈ S, (((component d i).card : ℤ)-1)) =
      2 * ∑ A ∈ componentBlocks d S, (A.card.choose 2 : ℤ) := by
  classical
  calc
    _ = ∑ A ∈ componentBlocks d S, ∑ i ∈ A, (((component d i).card : ℤ)-1) := by
      have h := Finset.sum_biUnion (f := fun i => ((component d i).card : ℤ)-1)
        (component_blocks_disjoint d S)
      simpa only [component_blocks_union d S hclosed,id_eq] using h
    _ = ∑ A ∈ componentBlocks d S, 2*(A.card.choose 2 : ℤ) := by
      apply Finset.sum_congr rfl
      intro A hA
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
      have he (i : Fin n) (hi : i ∈ component d a) : component d i = component d a :=
        (component_eq_of_path d ((mem_component d a i).mp hi)).symm
      have hs : (∑ i ∈ component d a, (((component d i).card : ℤ)-1)) =
          ∑ _i ∈ component d a, (((component d a).card : ℤ)-1) :=
        Finset.sum_congr rfl (fun i hi => by rw [he i hi])
      rw [hs]
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact (FiniteCuts.twice_choose_two_int (component d a).card).symm
    _ = _ := by rw [Finset.mul_sum]

#print axioms component_blocks_card_sum
#print axioms component_blocks_capacity_sum
end LRX.CycleFootprint
