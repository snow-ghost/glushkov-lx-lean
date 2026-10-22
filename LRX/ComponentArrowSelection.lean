import LRX.ComponentSignedArrows

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Choose one real arrow per disjoint original component with exact count
and a total-length bound. -/
theorem select_component_arrows (p : State n) (T : Finset (Finset (Fin n)))
    (hT : T ⊆ suffixComponents p 0) (P : Fin n → Prop)
    (hex : ∀ C ∈ T, ∃ i ∈ C, P i) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, P i) ∧ S.card = T.card ∧
      (∑ i ∈ S, |displacement p.symm i|) ≤ ∑ C ∈ T, ((C.card : ℤ)-1) := by
  classical
  let pick (C : {C // C ∈ T}) : Fin n := Classical.choose (hex C.val C.property)
  have hpick (C : {C // C ∈ T}) : pick C ∈ C.val ∧ P (pick C) :=
    Classical.choose_spec (hex C.val C.property)
  have hinj : Function.Injective pick := by
    intro C D he
    apply Subtype.ext
    by_contra hne
    have hd := CycleFootprint.component_blocks_disjoint (displacement p.symm) (suffixVertices n 0)
      (hT C.property) (hT D.property) hne
    exact Finset.disjoint_left.mp hd (hpick C).1 (he ▸ (hpick D).1)
  let S := T.attach.image pick
  refine ⟨S,?_,?_,?_⟩
  · intro i hi
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hi
    exact (hpick C).2
  · simp only [S,Finset.card_image_of_injective _ hinj,Finset.card_attach]
  · rw [show S = T.attach.image pick from rfl,
      Finset.sum_image (fun i _ j _ hij => hinj hij)]
    calc
      _ ≤ ∑ C ∈ T.attach, ((C.val.card : ℤ)-1) := by
        apply Finset.sum_le_sum
        intro C hC
        obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (hT C.property)
        have hi : pick C ∈ componentSet p a := by rw [show componentSet p a = C.val from he]; exact (hpick C).1
        have h := component_arrow_length p a (pick C) hi
        change |displacement p.symm (pick C)| ≤ ((componentSet p a).card : ℤ)-1 at h
        rw [show componentSet p a = C.val from he] at h
        exact h
      _ = _ := Finset.sum_attach T (fun C : Finset (Fin n) => (C.card : ℤ)-1)

/-- The two original sign selections required for the exterior short-arrow bound. -/
theorem suffix_component_arrow_selections (p : State n) (L : ℕ) :
    let T := nontrivialSuffixComponents p L
    ∃ P N : Finset (Fin n),
      (∀ i ∈ P, 0 < displacement p.symm i) ∧
      (∀ i ∈ N, displacement p.symm i < 0) ∧
      P.card = T.card ∧ N.card = T.card ∧
      (∑ i ∈ P, |displacement p.symm i|) ≤ (∑ C ∈ T, ((C.card : ℤ)-1)) ∧
      (∑ i ∈ N, |displacement p.symm i|) ≤ (∑ C ∈ T, ((C.card : ℤ)-1)) := by
  classical
  let T := nontrivialSuffixComponents p L
  have hT : T ⊆ suffixComponents p 0 := by
    intro C hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr ⟨a,by simp,rfl⟩
  have hex (C : Finset (Fin n)) (hC : C ∈ T) :
      (∃ i ∈ C, 0 < displacement p.symm i) ∧ (∃ i ∈ C, displacement p.symm i < 0) := by
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC
    exact component_signed_arrows p a hsize
  obtain ⟨P,hP,hPc,hPb⟩ := select_component_arrows p T hT (fun i => 0 < displacement p.symm i)
    (fun C hC => (hex C hC).1)
  obtain ⟨N,hN,hNc,hNb⟩ := select_component_arrows p T hT (fun i => displacement p.symm i < 0)
    (fun C hC => (hex C hC).2)
  exact ⟨P,N,hP,hN,hPc,hNc,hPb,hNb⟩

#print axioms select_component_arrows
#print axioms suffix_component_arrow_selections
end LRX.FiniteCuts
