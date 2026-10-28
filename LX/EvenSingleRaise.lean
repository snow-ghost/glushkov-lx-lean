import LX.AntipodeCandidates
import LX.EvenCenteredMass
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

def evenBase (m : ℕ) (c : Fin n) : Fin n → ℤ :=
  perturbedBoard m ((c : ℤ)+1) (Equiv.swap 1 2)

theorem even_base_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n) :
    -(n : ℤ) ≤ ∑ i,evenBase m c i := even_perturbed_board_mass m hm hn ((c : ℤ)+1)

theorem even_base_bounds (m : ℕ) (c i : Fin n) :
    -(m : ℤ) ≤ evenBase m c i ∧ evenBase m c i < (n : ℤ)-m := center_bounds m _

theorem even_base_residue (m : ℕ) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d) (i : Fin n) :
    (d i : Fin n)=(evenBase m c i : Fin n) := by
  have hh := LX.Core.AffineLift.lift_residue hd i
  simp only [even,Equiv.symm_symm,Equiv.Perm.mul_apply,LX.Core.WordReflection.reflection_apply,
    Int.cast_natCast,Fin.cast_val_eq_self] at hh
  change (d i : Fin n)=(center (n := n) m (((c : ℤ)+1)-((Equiv.swap (1 : Fin n) 2) i : ℤ)-(i : ℤ)) : Fin n)
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
  linear_combination hh

theorem even_lift_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d)
    (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=evenBase m c ∨ ∃ a,d=raiseAt (evenBase m c) a := by
  exact balanced_single_raise m d (evenBase m c) hd.1 hlo
    (even_base_bounds m c) (even_base_residue m c hd) (even_base_mass m hm hn c)


#print axioms even_lift_single_raise
end LX.Antipode
