import LRX.BalancedSubsetEnergy

/-! Exact subset capacity for injective integer coordinates in a finite
interval. The endpoints need not be consecutive. -/
namespace LRX.FiniteCoordinates
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem range_sum_twice (k : ℕ) : 2*(∑ i ∈ Finset.range k, (i : ℤ))=(k : ℤ)*(k-1) := by
  by_cases hk : k=0
  · simp [hk]
  · have h := Finset.sum_range_id_mul_two k
    have hz := congrArg (fun a : ℕ => (a : ℤ)) h
    push_cast at hz
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hz
    norm_num at hz
    nlinarith

theorem sum_coordinate_difference (S : Finset α) (f g : α → ℤ) (L : ℤ)
    (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (hlo : ∀ i ∈ S, 0 ≤ f i) (hhi : ∀ i ∈ S, g i < L) :
    (∑ i ∈ S, (g i-f i)) ≤ (S.card : ℤ)*(L-S.card) := by
  classical
  have hlow := Finset.sum_range_le_sum (s := S.image f) (c := 0) (by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact hlo i hi)
  have hhigh := Finset.sum_le_sum_range (s := S.image g) (c := L-1) (by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have h := hhi i hi
    omega)
  rw [Finset.card_image_iff.mpr hf,Finset.sum_image hf] at hlow
  rw [Finset.card_image_iff.mpr hg,Finset.sum_image hg] at hhigh
  simp only [zero_add] at hlow
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hhigh
  rw [Finset.sum_sub_distrib]
  have hsum := range_sum_twice S.card
  nlinarith

theorem energy_capacity (S : Finset α) (f g : α → ℤ) (L : ℕ)
    (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (hflo : ∀ i ∈ S, 0 ≤ f i) (hfhi : ∀ i ∈ S, f i < L)
    (hglo : ∀ i ∈ S, 0 ≤ g i) (hghi : ∀ i ∈ S, g i < L)
    (hbalance : ∑ i ∈ S, (g i-f i)=0) (hcard : S.card ≤ L) :
    (∑ i ∈ S, |g i-f i|) ≤ 2*(S.card/2 : ℕ)*((L : ℤ)-(S.card/2 : ℕ)) := by
  classical
  let P := S.filter (fun i => 0 < g i-f i)
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hpc : P.card ≤ S.card := Finset.card_le_card hPS
  have point (i : α) : |g i-f i|=2*(if 0 < g i-f i then g i-f i else 0)-(g i-f i) := by
    split_ifs with hi
    · rw [abs_of_pos hi]; omega
    · rw [abs_of_nonpos (by omega : g i-f i ≤ 0)]; omega
  have hmass : (∑ i ∈ S, |g i-f i|)=2*∑ i ∈ P, (g i-f i) := by
    conv_lhs => rw [Finset.sum_congr rfl (fun i _ => point i),Finset.sum_sub_distrib,← Finset.mul_sum,hbalance,sub_zero]
    simp only [P,Finset.sum_filter]
  have hpos := sum_coordinate_difference P f g L (hf.mono hPS) (hg.mono hPS)
    (fun i hi => hflo i (hPS hi)) (fun i hi => hghi i (hPS hi))
  have hNS : S\P ⊆ S := Finset.sdiff_subset
  have hneg := sum_coordinate_difference (S\P) g f L (hg.mono hNS) (hf.mono hNS)
    (fun i hi => hglo i (hNS hi)) (fun i hi => hfhi i (hNS hi))
  have hsum := Finset.sum_sdiff hPS (f := fun i => g i-f i)
  rw [hbalance] at hsum
  have hsign : (∑ i ∈ S\P, (f i-g i))= -(∑ i ∈ S\P, (g i-f i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsign,Finset.card_sdiff_of_subset hPS,Nat.cast_sub hpc] at hneg
  have hhalf : 2*(S.card/2) ≤ L := by omega
  by_cases hp : P.card ≤ S.card/2
  · have h1 : (P.card : ℤ) ≤ (S.card/2 : ℕ) := by exact_mod_cast hp
    have h2 : (0 : ℤ) ≤ (L : ℤ)-(S.card/2 : ℕ)-P.card := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]
  · have h1 : (S.card : ℤ)-P.card ≤ (S.card/2 : ℕ) := by omega
    have h2 : (0 : ℤ) ≤ (L : ℤ)-(S.card/2 : ℕ)-((S.card : ℤ)-P.card) := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]

#print axioms sum_coordinate_difference
#print axioms energy_capacity
end LRX.FiniteCoordinates
