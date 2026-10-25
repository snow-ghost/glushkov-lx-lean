import LX.DepthBound
import LX.PhaseExchangePrice
import LX.PhaseMinimumRescue
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem raise_coordinate_crossing (d : Fin n → ℤ) (a i j : Fin n) :
    crossing (raiseMinimum d a) i j=crossing d i j+
      (if i=a then (1 : ℤ) else 0)-(if j=a then (1 : ℤ) else 0) := by
  rw [raiseMinimum,phase_shift_crossing]
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  by_cases hi : i=a <;> by_cases hj : j=a <;> simp [hi,hj] <;> ring

private theorem crossing_ge_neg_one (d : Fin n → ℤ)
    (hw : ∀ i j,d i-d j < (n : ℤ)) (i j : Fin n) : -1 ≤ crossing d i j := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have ht : crossingNumerator d i j < (2 : ℤ)*n := by
    have := hw j i
    have := (j-i).isLt
    unfold crossingNumerator
    omega
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr ht
  unfold crossing
  omega

private theorem abs_add_one_price (x : ℤ) (hx : -1 ≤ x) :
    |x+1|-|x|=1-2*((-x).toNat : ℤ) := by
  by_cases he : x= -1
  · subst x; norm_num
  · have hx0 : 0 ≤ x := by omega
    rw [abs_of_nonneg hx0,abs_of_nonneg (by omega : 0 ≤ x+1)]
    have hz : (-x).toNat=0 := by omega
    rw [hz]; ring

/-- Raising any coordinate has an exact price in terms of its backward
depth. A minimum-coordinate premise is unnecessary. -/
theorem raise_coordinate_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) (hw : ∀ i j,d i-d j < (n : ℤ)) :
    (inversions (raiseMinimum d a) : ℤ)-inversions d=
      (n : ℤ)-1-2*(backwardDepth d a : ℤ) := by
  let Δ : Fin n → ℤ := fun j => if j=a then 0 else |crossing d a j+1|-|crossing d a j|
  have hpoint (i j : Fin n) :
      |crossing (raiseMinimum d a) i j|-|crossing d i j|=
        (if i=a then Δ j else 0)+(if j=a then Δ i else 0) := by
    rw [raise_coordinate_crossing]
    by_cases hi : i=a
    · subst i
      by_cases hj : j=a
      · subst j; simp [Δ]
      · simp [Δ,hj]
    · by_cases hj : j=a
      · subst j
        simp only [ite_eq_right hi,ite_true,zero_add,add_zero,Δ]
        rw [crossing_antisymm hd i a]
        rw [show -crossing d a i-1= -(crossing d a i+1) by ring,abs_neg,abs_neg]
      · simp [hi,hj]
  have hterm (j : Fin n) : Δ j=
      1-(if j=a then (1 : ℤ) else 0)-2*((-crossing d a j).toNat : ℤ) := by
    by_cases hj : j=a
    · subst j; simp [Δ]
    · simp only [Δ,ite_eq_right hj,sub_zero]
      exact abs_add_one_price _ (crossing_ge_neg_one d hw a j)
  have hsumΔ : (∑ j : Fin n,Δ j)=(n : ℤ)-1-2*(backwardDepth d a : ℤ) := by
    simp only [hterm,Finset.sum_sub_distrib,← Finset.mul_sum,backwardDepth,Nat.cast_sum]
    simp
  have hs : (∑ i : Fin n,∑ j : Fin n,
      (|crossing (raiseMinimum d a) i j|-|crossing d i j|))=2*(∑ j : Fin n,Δ j) := by
    simp only [hpoint,Finset.sum_add_distrib]
    have h1 : (∑ i : Fin n,∑ j : Fin n,if i=a then Δ j else 0)=∑ j : Fin n,Δ j := by simp
    have h2 : (∑ i : Fin n,∑ j : Fin n,if j=a then Δ i else 0)=∑ j : Fin n,Δ j := by simp
    rw [h1,h2]; ring
  have hold : 2*(inversions d : ℤ)=∑ i : Fin n,∑ j : Fin n,|crossing d i j| := by
    change 2*(LRX.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=_
    have hh := congrArg (fun k : ℕ => (k : ℤ)) (LRX.RotationWords.twice_inversion_count hd)
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hh
  have hnew : 2*(inversions (raiseMinimum d a) : ℤ)=
      ∑ i : Fin n,∑ j : Fin n,|crossing (raiseMinimum d a) i j| := by
    change 2*(LRX.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+raiseMinimum d a i) : ℤ)=_
    have hh := congrArg (fun k : ℕ => (k : ℤ))
      (LRX.RotationWords.twice_inversion_count (raise_minimum_lift hd a))
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hh
  simp only [Finset.sum_sub_distrib] at hs
  rw [← hold,← hnew,hsumΔ] at hs
  omega

theorem raise_coordinate_inversions_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) (hw : ∀ i j,d i-d j < (n : ℤ))
    (h : ℕ) (hlo : ∀ i,-(h : ℤ) ≤ d i) :
    (inversions d : ℤ)+(n : ℤ)-1-2*h ≤ inversions (raiseMinimum d a) := by
  have he := raise_coordinate_inversions hd a hw
  have hb := backward_depth_le_strip hd (h : ℤ) hlo a
  omega

#print axioms raise_coordinate_inversions
#print axioms raise_coordinate_inversions_lower
end LX.AffineScan
