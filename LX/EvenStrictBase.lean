import LX.AntipodeCandidates
import LX.AntipodeProfileCertificates
import LX.EvenCenteredMass
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem center_predecessor (m : ℕ) (hm : 1 ≤ m) (z : ℤ) :
    center (n := n) (m-1) z=center (n := n) m (z-1)+1 := by
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have he : z+((m-1 : ℕ) : ℤ)=(z-1)+m := by omega
  unfold center
  rw [he]
  omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

def evenStrictBase (m : ℕ) (c : Fin n) : Fin n → ℤ :=
  perturbedBoard (m-1) ((c : ℤ)+1) (Equiv.swap 1 2)

theorem even_strict_base_shift (m : ℕ) (hm : 1 ≤ m) (c i : Fin n) :
    evenStrictBase m c i=perturbedBoard m (c : ℤ) (Equiv.swap 1 2) i+1 := by
  unfold evenStrictBase perturbedBoard
  rw [center_predecessor m hm]
  congr 2
  ring

theorem even_strict_base_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n) :
    0 ≤ ∑ i,evenStrictBase m c i := by
  simp only [even_strict_base_shift m (by omega),Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hh := even_perturbed_board_mass m hm hn (c : ℤ)
  omega

theorem even_strict_base_labels (m : ℕ) (c i : Fin n) :
    i+(evenStrictBase m c i : Fin n)=(even : State n).symm i+c := by
  rw [show (even : State n).symm i=1-Equiv.swap (1 : Fin n) 2 i from rfl]
  change i+(perturbedBoard (m-1) ((c : ℤ)+1) (Equiv.swap (1 : Fin n) 2) i : Fin n)=_
  rw [perturbed_board_labels]
  simp only [Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
  ring

/-- Balance makes the narrower strip representative unique; there is no
remaining coordinate choice in the even case. -/
theorem even_strict_lift_unique (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n)
    {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) : d=evenStrictBase m c := by
  have hbounds (i : Fin n) :
      -((m-1 : ℕ) : ℤ) ≤ evenStrictBase m c i ∧ evenStrictBase m c i < (n : ℤ)-(m-1 : ℕ) :=
    center_bounds (m-1) _
  have hres (i : Fin n) : (d i : Fin n)=(evenStrictBase m c i : Fin n) := by
    have hh := lift_residue hd i
    have he := even_strict_base_labels m c i
    simp only [Int.cast_natCast,Fin.cast_val_eq_self] at hh
    exact add_left_cancel (hh.trans he.symm)
  have hmlo (i : Fin n) : -((m-1 : ℕ) : ℤ) ≤ d i := by have := hlo i; omega
  have hmass := even_strict_base_mass m hm hn c
  rcases balanced_single_raise (m-1) d (evenStrictBase m c) hd.1 hmlo hbounds hres
      (by have := NeZero.pos n; omega) with he | ⟨a,ha⟩
  · exact he
  · have hz := hd.1
    rw [ha] at hz
    have hs : (∑ i : Fin n,raiseAt (evenStrictBase m c) a i)=
        (∑ i : Fin n,evenStrictBase m c i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
    rw [hs] at hz
    have := NeZero.pos n
    omega


#print axioms even_strict_lift_unique
end LX.Antipode
