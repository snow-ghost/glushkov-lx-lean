import LX.LiftedModel
import Mathlib

/-! Swapping the endpoints of a zero gap gives a balanced shorter lift.
The exact drop in displacement mass is twice the gap length. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def exchange (d : Fin n → ℤ) (v i : Fin n) : ℤ :=
  if i=0 then (v : ℤ)+d v else if i=v then d 0-(v : ℤ) else d i

theorem exchange_sum (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0) (f : ℤ → ℤ) :
    (∑ i : Fin n, f (exchange d v i))=(∑ i : Fin n, f (d i))+
      (f ((v : ℤ)+d v)-f (d 0))+(f (d 0-(v : ℤ))-f (d v)) := by
  have hpoint (i : Fin n) : f (exchange d v i)=f (d i)+
      (if i=0 then f ((v : ℤ)+d v)-f (d 0) else 0)+
      (if i=v then f (d 0-(v : ℤ))-f (d v) else 0) := by
    by_cases hi : i=0
    · subst i
      simp [exchange,hv,Ne.symm hv]
    · by_cases hiv : i=v
      · subst i
        simp [exchange,hv]
      · simp [exchange,hi,hiv]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem exchange_balance (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0) (hd : ∑ i, d i=0) :
    (∑ i, exchange d v i)=0 := by
  have h := exchange_sum d v hv id
  simp only [id_eq,hd] at h
  omega

theorem exchange_mass (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0)
    (hpos : (v : ℤ) ≤ d 0) (hneg : (v : ℤ) ≤ -d v) :
    (∑ i : Fin n, |exchange d v i|)=(∑ i : Fin n, |d i|)-2*(v : ℤ) := by
  have h := exchange_sum d v hv (fun z => |z|)
  have hv0 : (0 : ℤ) ≤ v := by positivity
  rw [abs_of_nonpos (by omega : (v : ℤ)+d v ≤ 0),abs_of_nonneg (by omega : 0 ≤ d 0),
    abs_of_nonneg (by omega : 0 ≤ d 0-(v : ℤ)),abs_of_nonpos (by omega : d v ≤ 0)] at h
  omega

theorem exchange_short (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0)
    (hpos : (v : ℤ) ≤ d 0) (hneg : (v : ℤ) ≤ -d v)
    (hshort : ∀ i, 2*|d i| < (n : ℤ)) (i : Fin n) : 2*|exchange d v i| < (n : ℤ) := by
  have hv0 : (0 : ℤ) ≤ v := by positivity
  by_cases hi : i=0
  · subst i
    simp only [exchange,ite_true]
    rw [abs_of_nonpos (by omega : (v : ℤ)+d v ≤ 0)]
    have h := hshort v
    rw [abs_of_nonpos (by omega : d v ≤ 0)] at h
    omega
  · by_cases hiv : i=v
    · subst i
      simp only [exchange,ite_eq_right hv,ite_true]
      rw [abs_of_nonneg (by omega : 0 ≤ d 0-(v : ℤ))]
      have h := hshort 0
      rw [abs_of_nonneg (by omega : 0 ≤ d 0)] at h
      omega
    · simpa only [exchange,ite_eq_right hi,ite_eq_right hiv] using hshort i

theorem exchange_lift {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (v : Fin n) (hv : v ≠ 0) :
    AffineLift.IsLift (Equiv.swap 0 v*p) 0 (exchange d v) := by
  refine ⟨exchange_balance d v hv hd.1,?_⟩
  intro i
  change Int.ModEq (n : ℤ) ((i : ℤ)+exchange d v i) ((p.symm (Equiv.swap 0 v i) : ℤ)+0)
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  simp only [Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self,Int.cast_zero,add_zero]
  by_cases hi : i=0
  · subst i
    simp only [exchange,ite_true,Equiv.swap_apply_left,Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self,zero_add]
    simpa only [Int.cast_zero,add_zero] using AffineLift.lift_residue hd v
  · by_cases hiv : i=v
    · subst i
      simp only [exchange,ite_eq_right hv,ite_true,Equiv.swap_apply_right,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
      have h := AffineLift.lift_residue hd (0 : Fin n)
      simp only [Int.cast_zero,add_zero,zero_add] at h
      linear_combination h
    · simp only [exchange,ite_eq_right hi,ite_eq_right hiv,Equiv.swap_apply_of_ne_of_ne hi hiv]
      simpa only [Int.cast_zero,add_zero] using AffineLift.lift_residue hd i

#print axioms exchange_mass
#print axioms exchange_short
#print axioms exchange_lift
end LX.Core.ZeroGap
