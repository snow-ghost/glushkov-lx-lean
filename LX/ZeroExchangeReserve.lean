import LRX.CapacityEqualityReflection
import LRX.NarrowWindowLift
import LX.MinimumEnergyPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.RotationWords
variable {n : ℕ} [NeZero n]

/-- The LRX equality classification applies to the actual LX phase after a
proved output shift. Its conclusion is pulled back to the original input. -/
theorem majorized_capacity_reflection {p : State n} {c₀ : ℤ} {d : Fin n → ℤ}
    (hsource : IsLift p.symm c₀ d) (hm : Majorized d)
    (heq : (inversions d : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ r : Fin n,∀ i,p i=r-i := by
  let c : Fin n := (c₀ : Fin n)
  let q : State n := (p.trans (Equiv.addRight c)).symm
  have hq (i : Fin n) : q.symm i=p i+c := rfl
  have hd : IsLift q 0 d := by
    refine ⟨hsource.1,?_⟩
    intro i
    apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self,Int.cast_zero,add_zero,hq]
    exact lift_residue hsource i
  have hshort := LRX.FiniteWindow.majorized_short hd hm
  have hx : (LRX.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := heq
  obtain ⟨t,ht⟩ := LRX.FiniteCuts.strict_capacity_equality_reflection hd.1 hm hd hshort
    (fun _ hh => hh) (fun _ hh => hh) hx
  refine ⟨t+t-(((n-1)/2 : ℕ) : Fin n)-c,?_⟩
  intro i
  have hh := ht (i-t)
  rw [local_target_inverse,hq,sub_add_cancel] at hh
  simp only [zero_sub,Int.cast_natCast] at hh
  linear_combination hh

theorem zero_exchange_reserve_reflection {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (heq : (inversions (displacement p a) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ r : Fin n,∀ i,p i=r-i :=
  majorized_capacity_reflection (is_lift p a) (global_minimum_majorized ha) heq


#print axioms majorized_capacity_reflection
#print axioms zero_exchange_reserve_reflection
end LX.AnchoredPhases
