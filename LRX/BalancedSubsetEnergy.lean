import LRX.PacketCoreBalance

/-! Majorization bounds the energy of any balanced subset by its number of
positions. No separate majorization assumption on the pruned lift is needed. -/
namespace LRX.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem majorized_neg {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : Majorized d) :
    Majorized (fun i => -d i) := by
  intro S
  have hs := Finset.sum_add_sum_compl S d
  rw [hd] at hs
  have hc : S.card ≤ n := by simpa using Finset.card_le_univ S
  have h := hm Sᶜ
  simp only [Finset.card_compl,Finset.card_univ,Fintype.card_fin,Nat.cast_sub hc] at h
  rw [Finset.sum_neg_distrib]
  nlinarith

theorem subset_displacement_balance (d : Fin n → ℤ) (S : Finset (Fin n))
    (hd : ∑ i ∈ S, d i=0) :
    (∑ i ∈ S, |d i|)=2*∑ i ∈ S.filter (fun i => 0 < d i), d i := by
  have point (i : Fin n) : |d i|=2*(if 0 < d i then d i else 0)-d i := by
    split_ifs with hi
    · rw [abs_of_pos hi]; omega
    · rw [abs_of_nonpos (by omega : d i ≤ 0)]; omega
  simp only [point,Finset.sum_sub_distrib,← Finset.mul_sum,hd,sub_zero,Finset.sum_filter]

theorem balanced_subset_energy {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : Majorized d)
    (S : Finset (Fin n)) (hS : ∑ i ∈ S, d i=0) :
    (∑ i ∈ S, |d i|) ≤ (S.card/2 : ℕ)*((n : ℤ)-(S.card/2 : ℕ)) := by
  classical
  let P := S.filter (fun i => 0 < d i)
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hpc : P.card ≤ S.card := Finset.card_le_card hPS
  have hsc : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hmass : (∑ i ∈ S, |d i|)=2*∑ i ∈ P, d i := subset_displacement_balance d S hS
  have hpos : (∑ i ∈ S, |d i|) ≤ (P.card : ℤ)*(n-P.card) := by rw [hmass]; exact hm P
  have hsum := Finset.sum_sdiff hPS (f := d)
  have hneg := majorized_neg hd hm (S\P)
  simp only [Finset.sum_neg_distrib,Finset.card_sdiff_of_subset hPS,Nat.cast_sub hpc] at hneg
  have hmassneg : (∑ i ∈ S, |d i|) ≤ ((S.card : ℤ)-P.card)*(n-((S.card : ℤ)-P.card)) := by
    rw [hS] at hsum
    nlinarith
  have hhalf : 2*(S.card/2) ≤ n := by omega
  by_cases hp : P.card ≤ S.card/2
  · have h1 : (P.card : ℤ) ≤ (S.card/2 : ℕ) := by exact_mod_cast hp
    have h2 : (0 : ℤ) ≤ (n : ℤ)-(S.card/2 : ℕ)-P.card := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]
  · have h1 : (S.card : ℤ)-P.card ≤ (S.card/2 : ℕ) := by omega
    have h2 : (0 : ℤ) ≤ (n : ℤ)-(S.card/2 : ℕ)-((S.card : ℤ)-P.card) := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]

#print axioms balanced_subset_energy
end LRX.AffineLift
namespace LRX.PrunedLift
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

theorem core_energy_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) :
    (∑ i ∈ core p d 0, |d i|) ≤ ((core p d 0).card/2 : ℕ)*((n : ℤ)-((core p d 0).card/2 : ℕ)) :=
  AffineLift.balanced_subset_energy hd.1 hm (core p d 0) (core_balance hd hcover hroot)

#print axioms core_energy_bound
end LRX.PrunedLift
