import LX.AntipodeBoundaryPhase
import LX.AntipodeHeightReduction
import LX.AntipodeProfileCertificates
import LX.EvenBoundaryBase
import LX.ExceptionalPriceLower
import LX.SingleRaisePrice
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_exception_lift (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    IsLift (even : State n) ((m+3 : ℕ) : ℤ) (evenException m) := by
  refine ⟨even_exception_balance m hm hn,?_⟩
  intro i
  let c : Fin n := ((m+2 : ℕ) : Fin n)
  have hb := perturbed_board_labels m ((c : ℤ)+1) (Equiv.swap (1 : Fin n) 2) i
  change i+(evenBase m c i : Fin n)=_ at hb
  rw [even_boundary_base m hm hn] at hb
  apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp
  simp only [even,Equiv.symm_symm,Equiv.Perm.mul_apply,LX.Core.WordReflection.reflection_apply,
    Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self,
    c,Nat.cast_add,Nat.cast_ofNat] at hb ⊢
  linear_combination hb

theorem even_exception_strip (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (i : Fin n) :
    1-(m : ℤ) ≤ evenException m i ∧ evenException m i ≤ (m : ℤ) := by
  have hh := even_base_bounds m (((m+2 : ℕ)) : Fin n) i
  rw [even_boundary_base m hm hn] at hh
  omega

/-- Every lower-strip lift in phase m+2 has two more inversions than the
coarse uniform lower estimate. This closes the boundary-height branch. -/
theorem even_boundary_inversions_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hc : c=((m+2 : ℕ) : Fin n)) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    m*(m-1)+1 ≤ inversions d := by
  subst c
  rcases even_lift_single_raise m (by omega) hn (((m+2 : ℕ)) : Fin n) hd hlo with hbase | ⟨a,ha⟩
  · have hz := hd.1
    rw [hbase,even_boundary_base_mass m hm hn] at hz
    have := NeZero.pos n
    omega
  · have hsource := even_exception_lift m hm hn
    have hw : ∀ i j : Fin n,evenException m i-evenException m j < (n : ℤ) := by
      intro i j
      have hi := even_exception_strip m hm hn i
      have hj := even_exception_strip m hm hn j
      omega
    have hlow : ∀ i,-(((m-1 : ℕ) : ℤ)) ≤ evenException (n := n) m i := by
      intro i
      have hh := even_exception_strip m hm hn i
      omega
    have he : d=raiseMinimum (evenException m) a := by
      rw [ha]
      funext i
      rw [raise_minimum_apply]
      simp only [raiseAt,even_boundary_base m hm hn,Nat.cast_ite,Nat.cast_zero]
    have hprice := raise_coordinate_inversions_lower hsource a hw (m-1) hlow
    rw [← he] at hprice
    have hI := even_exception_inversions_lower m hm hn hsource
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions (evenException (n := n) m) : ℤ) := by
      exact_mod_cast hI
    have hgoal : (m : ℤ)*((m-1 : ℕ) : ℤ)+1 ≤ (inversions d : ℤ) := by
      have hn' : (n : ℤ)=2*m := by omega
      have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
      nlinarith
    exact_mod_cast hgoal

/-- A hypothetically shorter even word has no coordinate at height m.
Only the narrower strip remains for the general lower bound. -/
theorem even_unpaid_strict_lower_strip (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-4*m+3) :
    ∀ i,1-(m : ℤ) ≤ d i := by
  have hlo := even_unpaid_lower_strip m hm hn hd hg hu
  intro i
  by_contra hnot
  have hdi : d i= -(m : ℤ) := by have := hlo i; omega
  have hc := even_unpaid_boundary_phase m hm hn hd hg hu ⟨i,hdi⟩
  have hI := even_boundary_inversions_lower m hm hn hd hc hlo
  have hpos := even_unpaid_bottom_positions m hm hn hd hg hu i hdi
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd i
  have hrot : ((n : ℤ)-1)*(m : ℤ)-(n : ℤ)+2 ≤ (paidRotations c g : ℤ) := by
    rcases hpos with hi | hi
    · have he : i=1 := Fin.ext (by omega)
      subst i
      have hq : -(even : State n).symm 1=1 := by
        change -(1-Equiv.swap (1 : Fin n) 2 1)=1
        rw [Equiv.swap_apply_left]; ring
      rw [hq] at ht
      simp only [targets,hdi,hv1,Nat.sub_self,Nat.cast_zero,Nat.cast_one,mul_zero,zero_sub] at ht
      nlinarith
    · have he : i=2 := Fin.ext (by omega)
      subst i
      have hq : -(even : State n).symm 2=0 := by
        change -(1-Equiv.swap (1 : Fin n) 2 2)=0
        rw [Equiv.swap_apply_right]; ring
      rw [hq] at ht
      simp only [targets,hdi,hv2,Fin.val_zero,Nat.cast_zero,Nat.cast_ofNat,
        show (2-1 : ℕ)=1 by decide,Nat.cast_one,mul_one,add_zero] at ht
      nlinarith
  have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ)+1 ≤ (inversions d : ℤ) := by exact_mod_cast hI
  have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-4*m+3 : ℕ) : ℤ) := by
    exact_mod_cast hu
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hu'
  push_cast at hu'
  have hn' : (n : ℤ)=2*m := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  rw [hm1] at hI'
  nlinarith

#print axioms even_exception_lift
#print axioms even_boundary_inversions_lower
#print axioms even_unpaid_strict_lower_strip
end LX.Antipode
