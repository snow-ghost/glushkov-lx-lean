import LRX.InversionSet
import Mathlib

/-! The exact affine X price agrees with the crossing data derived from lifts. -/
namespace LRX.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem inversion_term_crossing (d : Fin n → ℤ) (i j : Fin n) (hij : i < j) :
    ((((j : ℤ)+d j)-((i : ℤ)+d i))/(n : ℤ)).natAbs=
      (AffineLift.crossing d i j).natAbs := by
  have hv : ((j-i : Fin n) : ℤ)=(j : ℤ)-(i : ℤ) := by
    rw [Fin.sub_val_of_le (le_of_lt hij), Nat.cast_sub (le_of_lt hij)]
  simp only [AffineLift.crossing, AffineLift.crossingNumerator, Int.natAbs_neg, hv]
  congr 2
  ring

omit [NeZero n] in
theorem inversion_count_crossings (d : Fin n → ℤ) :
    inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (AffineLift.crossing d i j).natAbs else 0 := by
  unfold inversionCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · exact inversion_term_crossing d i j hij
  · rfl

#print axioms inversion_count_crossings
end LRX.LiftedModel
