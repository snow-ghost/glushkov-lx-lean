import LX.DepthQueue
import LX.AnchoredPhases

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
    simpa only [labels,Equiv.symm_symm] using LRX.AffineLift.lift_residue hd i
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

/-- Every permutation has an actual word with the proved leading coefficient 3/4.
The linear error here is still too large for QuadraticUpperBound. -/
theorem exists_quadratic_coarse_word (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w=p ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2+2*n-5 := by
  obtain ⟨a,_,_,ha⟩ := exists_short_candidate p⁻¹
  obtain ⟨w,hw,hprice⟩ := candidate_word_bound hn p⁻¹ a
  refine ⟨w,?_,?_⟩
  · exact (inv_mul_eq_one.mp hw).symm
  · have hh : 2*(height p⁻¹ a : ℤ) ≤ (n : ℤ)-1 := by omega
    have hpos : (0 : ℤ) ≤ n := Nat.cast_nonneg _
    have ht := mul_nonneg hpos (show (0 : ℤ) ≤ (n : ℤ)-2*height p⁻¹ a-1 by omega)
    have hs := sq_nonneg ((n : ℤ)-2*height p⁻¹ a-2)
    nlinarith

/-- The requested negative linear term already holds when an anchored lift
has height at least three below half the dimension. -/
theorem low_height_word (hn : 2 ≤ n) (p : State n) (a : Fin n)
    (ha : 2*height p a+6 ≤ n) :
    ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n := by
  obtain ⟨w,hw,hprice⟩ := candidate_word_bound hn p a
  refine ⟨w,hw,?_⟩
  have hh : 2*(height p a : ℤ)+6 ≤ (n : ℤ) := by exact_mod_cast ha
  have ht := mul_nonneg (Nat.cast_nonneg n : (0 : ℤ) ≤ n)
    (show (0 : ℤ) ≤ (n : ℤ)-2*height p a-6 by omega)
  have hs := sq_nonneg ((n : ℤ)-2*height p a-2)
  nlinarith

#print axioms candidate_word_bound
#print axioms exists_quadratic_coarse_word
#print axioms low_height_word
end LX.AnchoredPhases

namespace LX

theorem diameter_coarse_quadratic (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    4*(diameter n : ℤ) ≤ 3*(n : ℤ)^2+2*n-5 := by
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (State n)) ⟨1, Finset.mem_univ _⟩ length
  obtain ⟨w,hw,hprice⟩ := AnchoredPhases.exists_quadratic_coarse_word hn p
  have hlen := length_le_word (n := n) w
  rw [hw] at hlen
  have he : diameter n=length p := hp
  rw [he]
  omega

#print axioms diameter_coarse_quadratic
end LX
