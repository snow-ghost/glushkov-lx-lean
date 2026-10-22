import LRX.ComponentArrowSelection

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Remove one arrow of each sign per selected component and apply capacity
only to the remaining original arrows. -/
theorem suffix_component_tail_capacity (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (L : ℕ) :
    let T := nontrivialSuffixComponents p L
    let t := T.card
    let v := ∑ C ∈ T, C.card
    ∃ k : ℕ, t ≤ k ∧ k ≤ n/2 ∧ n-p.support.card ≤ n-2*k ∧
      (∑ i, |displacement p.symm i|) ≤ 2*((v : ℤ)-(t : ℤ))+
        ((k-t : ℕ) : ℤ)*((n : ℤ)-((k-t : ℕ) : ℤ)) := by
  classical
  let T := nontrivialSuffixComponents p L
  let t := T.card
  let v := ∑ C ∈ T, C.card
  let P₀ := Finset.univ.filter (fun i : Fin n => 0 < displacement p.symm i)
  let N₀ := Finset.univ.filter (fun i : Fin n => displacement p.symm i < 0)
  obtain ⟨P,N,hP,hN,hPc,hNc,hPb,hNb⟩ := suffix_component_arrow_selections p L
  have hPs : P ⊆ P₀ := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP i hi⟩
  have hNs : N ⊆ N₀ := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hN i hi⟩
  have htp : t ≤ P₀.card := by have h := Finset.card_le_card hPs; rw [hPc] at h; exact h
  have htn : t ≤ N₀.card := by have h := Finset.card_le_card hNs; rw [hNc] at h; exact h
  have hdis : Disjoint P₀ N₀ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp := (Finset.mem_filter.mp hi).2
    have hn := (Finset.mem_filter.mp hj).2
    omega
  have hunion : P₀ ∪ N₀ = p.support := by
    ext i
    simp only [P₀,N₀,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,mem_support_inverse]
    constructor
    · intro h he
      simp only [displacement,he,sub_self,lt_self_iff_false,or_self] at h
    · intro h
      have hv : (p.symm i).val ≠ i.val := fun he => h (Fin.ext he)
      unfold displacement
      omega
  have hcount : P₀.card+N₀.card = p.support.card := by rw [← hunion,Finset.card_union_of_disjoint hdis]
  have hsupport : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  let k := min P₀.card N₀.card
  have hkp : k ≤ P₀.card := Nat.min_le_left _ _
  have hkn : k ≤ N₀.card := Nat.min_le_right _ _
  have htk : t ≤ k := Nat.le_min.mpr ⟨htp,htn⟩
  have hkhalf : k ≤ n/2 := by omega
  have hf : n-p.support.card ≤ n-2*k := by omega
  have hd := canonical_lift p.symm
  have hpos := AffineLift.selected_positive_residual (displacement p.symm) hd.1 hmaj P hPs
  have hneg := AffineLift.original_selected_negative_residual hd.1 hmaj
    (Function.Embedding.refl (Fin n)) (displacement p.symm) (fun _ => rfl) hd.1 N hNs
  rw [Finset.card_sdiff_of_subset hPs,hPc] at hpos
  rw [Finset.card_sdiff_of_subset hNs,hNc] at hneg
  have hcost : (∑ C ∈ T, ((C.card : ℤ)-1)) = (v : ℤ)-(t : ℤ) := by
    simp only [v,t,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_sum]
  change (∑ i ∈ P, |displacement p.symm i|) ≤ ∑ C ∈ T, ((C.card : ℤ)-1) at hPb
  change (∑ i ∈ N, |displacement p.symm i|) ≤ ∑ C ∈ T, ((C.card : ℤ)-1) at hNb
  rw [hcost] at hPb hNb
  refine ⟨k,htk,hkhalf,hf,?_⟩
  by_cases h : P₀.card ≤ N₀.card
  · have hk : k = P₀.card := Nat.min_eq_left h
    rw [hk]
    change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ P, |displacement p.symm i|)+
      ((P₀.card-t : ℕ) : ℤ)*((n : ℤ)-((P₀.card-t : ℕ) : ℤ)) at hpos
    linarith
  · have hk : k = N₀.card := Nat.min_eq_right (by omega)
    rw [hk]
    change (∑ i, |displacement p.symm i|) ≤ 2*(∑ i ∈ N, |displacement p.symm i|)+
      ((N₀.card-t : ℕ) : ℤ)*((n : ℤ)-((N₀.card-t : ℕ) : ℤ)) at hneg
    linarith

#print axioms suffix_component_tail_capacity
end LRX.FiniteCuts
