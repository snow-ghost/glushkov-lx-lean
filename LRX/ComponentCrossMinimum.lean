import LRX.LoadComponentPartition
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace LRX.FiniteCuts
open scoped BigOperators

/-- The cross-pair reserve of components of size at least two has the
quadratic lower bound used in C7. -/
theorem component_cross_minimum {α : Type*} (S : Finset α) (size : α → ℕ)
    (hsize : ∀ i ∈ S, 2 ≤ size i) :
    let v := ∑ i ∈ S, size i
    (v.choose 2 : ℤ) - (∑ i ∈ S, ((size i).choose 2 : ℤ)) ≥
      2*((S.card : ℤ)-1)*((v : ℤ)-(S.card : ℤ)) := by
  dsimp only
  have hx := Finset.sum_sq_le_sq_sum_of_nonneg (s := S)
    (f := fun i => (size i : ℤ)-2) (fun i hi => by have := hsize i hi; omega)
  have hsum : (∑ i ∈ S, ((size i : ℤ)-2)) = ((∑ i ∈ S, size i : ℕ) : ℤ)-2*(S.card : ℤ) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_sum]
    ring
  have hsquare : (∑ i ∈ S, ((size i : ℤ)-2)^2) =
      2*(∑ i ∈ S, ((size i).choose 2 : ℤ))-3*((∑ i ∈ S, size i : ℕ) : ℤ)+4*(S.card : ℤ) := by
    have hpoint (i : α) : ((size i : ℤ)-2)^2 = 2*((size i).choose 2 : ℤ)-3*(size i : ℤ)+4 := by
      have h := twice_choose_two_int (size i)
      nlinarith
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,Nat.cast_sum]
    ring
  rw [hsum,hsquare] at hx
  have hv := twice_choose_two_int (∑ i ∈ S, size i)
  nlinarith

/-- Additional isolated positions contribute all cross pairs and their own pairs. -/
theorem component_cross_minimum_with_isolated {α : Type*} (S : Finset α) (size : α → ℕ)
    (hsize : ∀ i ∈ S, 2 ≤ size i) (a : ℕ) :
    let v := ∑ i ∈ S, size i
    ((v+a).choose 2 : ℤ)-(∑ i ∈ S, ((size i).choose 2 : ℤ)) ≥
      2*((S.card : ℤ)-1)*((v : ℤ)-(S.card : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) := by
  dsimp only
  have h := component_cross_minimum S size hsize
  have hv := twice_choose_two_int (∑ i ∈ S, size i)
  have ha := twice_choose_two_int a
  have hva := twice_choose_two_int ((∑ i ∈ S, size i)+a)
  simp only [Nat.cast_add] at hva
  dsimp only at h
  nlinarith

#print axioms component_cross_minimum_with_isolated
end LRX.FiniteCuts
