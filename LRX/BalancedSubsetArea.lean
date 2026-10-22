import LRX.FiniteFillingEnergyBounds
import LRX.BalancedSubsetEnergy

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem displacement_zero_outside_support (p : State n) (i : Fin n) (hi : i ∉ p.support) :
    displacement p i = 0 := by
  have he : p i = i := by simpa only [Equiv.Perm.mem_support,not_not] using hi
  simp [displacement,he]

/-- Separate any selected positions from the remaining active positions. -/
theorem support_complement_sum (p : State n) (S : Finset (Fin n)) (g : Fin n → ℤ)
    (hz : ∀ i, i ∉ p.support → g i = 0) :
    (∑ i, g i) = (∑ i ∈ S, g i)+(∑ i ∈ p.support \ S, g i) := by
  classical
  have he : S ∪ (p.support \ S) = S ∪ p.support := by ext i; simp
  have hd : Disjoint S (p.support \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have ht : (∑ i ∈ S ∪ p.support, g i) = ∑ i, g i :=
    Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i (fun hs => hi (Finset.mem_union.mpr (Or.inr hs))))
  rw [← ht,← he,Finset.sum_union hd]

theorem four_capacity_parity_identity (n : ℕ) :
    4*((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))+(n%2 : ℕ) = (n : ℤ)^2 := by
  have hn : (n : ℤ) = 2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have hp : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hp with hp | hp <;> rw [hp] at hn ⊢ <;>
    simp only [Nat.cast_zero,Nat.cast_one,add_zero] at hn ⊢ <;> nlinarith

/-- The original majorization bounds the active complement of any balanced
selected set. This is the geometric prefix-square step in C9. -/
theorem balanced_subset_area_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p)) (S : Finset (Fin n))
    (hS : (∑ i ∈ S, displacement p i) = 0) :
    ((S.card : ℤ)+(((S ∪ p.support)ᶜ).card : ℤ))^2 ≤
      4*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-
        (∑ i, |displacement p i|)+(∑ i ∈ S, |displacement p i|))+(n%2 : ℕ) := by
  classical
  let R := p.support \ S
  let E := S ∪ p.support
  have hsplit := support_complement_sum p S (displacement p) (displacement_zero_outside_support p)
  have htotal : (∑ i, displacement p i) = 0 := (canonical_lift p).1
  have hR : (∑ i ∈ R, displacement p i) = 0 := by rw [htotal,hS] at hsplit; simpa only [zero_add] using hsplit.symm
  have hmass := support_complement_sum p S (fun i => |displacement p i|)
    (fun i hi => by rw [displacement_zero_outside_support p i hi,abs_zero])
  have hbound := AffineLift.balanced_subset_energy htotal hmaj R hR
  have he : S ∪ R = E := by dsimp [R,E]; ext i; simp
  have hd : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hcard : R.card+S.card+Eᶜ.card = n := by
    have hu := Finset.card_union_of_disjoint hd
    rw [he] at hu
    have hh := Finset.card_compl E
    have hn := Finset.card_le_univ E
    simp only [Fintype.card_fin] at hh hn
    omega
  have hhalf : 2*(R.card/2) ≤ R.card := by omega
  have hprod : 0 ≤ ((n : ℤ)-2*((R.card/2 : ℕ) : ℤ)-((S.card : ℤ)+(Eᶜ.card : ℤ)))*
      ((n : ℤ)-2*((R.card/2 : ℕ) : ℤ)+((S.card : ℤ)+(Eᶜ.card : ℤ))) :=
    mul_nonneg (by omega) (by omega)
  have hQ := four_capacity_parity_identity n
  change (∑ i, |displacement p i|) = (∑ i ∈ S, |displacement p i|)+(∑ i ∈ R, |displacement p i|) at hmass
  change ((S.card : ℤ)+(Eᶜ.card : ℤ))^2 ≤ _
  nlinarith

#print axioms balanced_subset_area_deficit
end LRX.FiniteCuts
