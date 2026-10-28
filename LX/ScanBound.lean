import LX.AnchoredPhases
import LX.DepthQueue
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- All exchanges, forward rotations, and the final orientation are charged. -/
theorem candidate_word_bound (hn : 2 ≤ n) (p : State n) (a : Fin n) :
    ∃ w : List Letter, p * eval w=1 ∧
      (w.length : ℤ) ≤ (height p a : ℤ)*(n-height p a-1) +
        (height p a+2)*(n-1) := by
  obtain ⟨w,ht,hw⟩ := candidate_sorting_word hn p a
  have hd := is_lift p a
  have hlabels (i : Fin n) : labels (displacement p a) i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using LX.Core.AffineLift.lift_residue hd i
  have hi : Function.Injective (labels (displacement p a)) := by
    intro i j hij
    rw [hlabels,hlabels] at hij
    exact p.injective (add_right_cancel hij)
  have hprice := candidate_price_components p a
  have hr := ht.rotations_le_depth hn hd.1 hi (height p a)
    (fun i => by exact_mod_cast hprice.2 i)
  refine ⟨paidWord (phase p a : Fin n) w,hw,?_⟩
  rw [ht.paid_length hn hd.1 hi, paidRotations]
  have hp := ((phase p a : Fin n)-(w.count .l : Fin n)).isLt
  have hrint : (w.count .l : ℤ) ≤ ((height p a : ℤ)+1)*((n-1 : ℕ) : ℤ) := by
    exact_mod_cast hr
  have hh : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
  rw [hh] at hrint
  push_cast
  nlinarith [hprice.1]


#print axioms candidate_word_bound
end LX.AnchoredPhases

namespace LX


end LX
