import LX.AntipodeHeightReduction
import LX.OddCenteredMass
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

def oddBase (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n) : Fin n → ℤ :=
  perturbedBoard m ((c : ℤ)+1) (oddRank m hm hn)

theorem odd_base_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n) :
    -(n : ℤ) ≤ ∑ i,oddBase m hm hn c i := by
  apply odd_perturbed_board_mass m hn ((c : ℤ)+1) (oddRank m hm hn)
  intro i
  change (i : ℤ)-(oddRankValue m i.val : ℤ) ≤ 1
  unfold oddRankValue
  split_ifs <;> omega

theorem odd_base_bounds (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c i : Fin n) :
    -(m : ℤ) ≤ oddBase m hm hn c i ∧ oddBase m hm hn c i < (n : ℤ)-m :=
  center_bounds m _

theorem odd_base_residue (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift (odd m hm hn) (c : ℤ) d) (i : Fin n) :
    (d i : Fin n)=(oddBase m hm hn c i : Fin n) := by
  have hh := LRX.AffineLift.lift_residue hd i
  simp only [odd,Equiv.symm_symm,Equiv.Perm.mul_apply,LRX.WordReflection.reflection_apply,
    Int.cast_natCast,Fin.cast_val_eq_self] at hh
  change (d i : Fin n)=(center (n := n) m (((c : ℤ)+1)-(oddRank m hm hn i : ℤ)-(i : ℤ)) : Fin n)
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
  linear_combination hh

/-- All balanced lifts in the surviving lower strip, at every phase,
are a fixed representative or a single-coordinate raise. -/
theorem odd_lift_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=oddBase m hm hn c ∨ ∃ a,d=raiseAt (oddBase m hm hn c) a := by
  exact balanced_single_raise m d (oddBase m hm hn c) hd.1 hlo
    (odd_base_bounds m hm hn c) (odd_base_residue m hm hn c hd) (odd_base_mass m hm hn c)

/-- Complete restriction of a putative cheaper word of the odd candidate
to n phases and at most n+1 explicitly described lifts per phase. -/
theorem odd_unpaid_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-m+1) :
    d=oddBase m hm hn c ∨ ∃ a,d=raiseAt (oddBase m hm hn c) a :=
  odd_lift_single_raise m hm hn c hd (odd_unpaid_lower_strip m hm hn hd hg hu)

#print axioms odd_lift_single_raise
#print axioms odd_unpaid_single_raise
end LX.Antipode
