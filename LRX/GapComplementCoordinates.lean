import LRX.PacketGapWidth
import LRX.FiniteCoordinateCapacity

/-! Finite coordinates on the complement of a packet gap retain every
physical distance. A shortest lifted arrow is no longer than its finite representative. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def complementCoordinate (r i : Fin n) : ℤ := (i : ℤ)-(r : ℤ)+if i=0 then (n : ℤ) else 0

theorem complement_coordinate_injective (r : Fin n) : Function.Injective (complementCoordinate r) := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  unfold complementCoordinate at he
  by_cases hi0 : i=0 <;> by_cases hj0 : j=0
  · exact hi0.trans hj0.symm
  · simp only [hi0,Fin.val_zero,Int.natCast_zero,ite_eq_left rfl,ite_eq_right hj0,add_zero] at he
    have hjn : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    omega
  · simp only [hj0,Fin.val_zero,Int.natCast_zero,ite_eq_left rfl,ite_eq_right hi0,add_zero] at he
    have hin : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    omega
  · simp only [ite_eq_right hi0,ite_eq_right hj0,add_zero] at he
    apply Fin.ext
    exact_mod_cast (show (i : ℤ)=(j : ℤ) by omega)

theorem complement_coordinate_bounds (p : State n) (d : Fin n → ℤ) (r : Fin n) (b : ℕ)
    (hr : r.val=b+1)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i)
    (i : Fin n) (hi : InCore p d 0 i) :
    0 ≤ complementCoordinate r i ∧ complementCoordinate r i < (n-b : ℕ) := by
  have hri := r.isLt
  have hii := i.isLt
  unfold complementCoordinate
  by_cases hi0 : i=0
  · simp [hi0]
    omega
  · have hin : 0 < i.val := by have h : i.val ≠ 0 := fun h => hi0 (Fin.ext h); omega
    have hir : r.val ≤ i.val := by by_contra h; exact hgap i hin (by omega) hi
    simp only [ite_eq_right hi0,add_zero]
    omega

theorem complement_coordinate_residue (r i : Fin n) :
    ((complementCoordinate r i : ℤ) : Fin n)=i-r := by
  unfold complementCoordinate
  split_ifs <;> simp

theorem shortest_representative {N a b : ℤ} (hN : 0 < N) (hshort : 2*|a| < N)
    (hm : Int.ModEq N a b) : |a| ≤ |b| := by
  by_contra h
  have hdiff : |a-b| < N := by have := abs_sub a b; omega
  have hmod : Int.ModEq N (a-b) 0 := by simpa using hm.sub_right b
  have hz : a-b=0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.modEq_zero_iff_dvd.mp hmod)
    have hh : ((a-b).natAbs : ℤ) < (N.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs,abs_of_pos hN] using hdiff
    exact_mod_cast hh
  have hab : a=b := by omega
  exact h (by rw [hab])

theorem displacement_le_complement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r i : Fin n) :
    |d i| ≤ |complementCoordinate r (p.symm i)-complementCoordinate r i| := by
  apply shortest_representative (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    (FiniteWindow.majorized_short hd hm i)
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  rw [Int.cast_sub,complement_coordinate_residue,complement_coordinate_residue]
  have h := AffineLift.lift_residue hd i
  linear_combination h

#print axioms complement_coordinate_bounds
#print axioms displacement_le_complement
end LRX.PrunedLift
