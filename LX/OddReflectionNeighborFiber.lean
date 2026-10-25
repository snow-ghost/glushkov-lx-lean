import LX.ReflectionPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Undoing an adjacent swap in an odd reflection creates exactly one
three-element raw-offset fiber. The third position is opposite the pair. -/
theorem odd_reflection_neighbor_fiber (p : State n) (r u : Fin n)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (m : ℕ) (hn : n=2*m+1) (hm : 2 ≤ m) (i : Fin n) :
    p i-i=p u-u ↔ i=u ∨ i=u+1 ∨ i=u+((m+1 : ℕ) : Fin n) := by
  let d : Fin n := u+((m+1 : ℕ) : Fin n)
  have hv : (((m+1 : ℕ) : Fin n)).val=m+1 := Nat.mod_eq_of_lt (by omega)
  have hv1 : (1 : Fin n).val=1 := by norm_num [Nat.mod_eq_of_lt (by omega : 1<n)]
  have hdu : d ≠ u := by
    intro he
    have he' : ((m+1 : ℕ) : Fin n)=0 := add_left_cancel (show u+((m+1 : ℕ) : Fin n)=u+0 by simpa [d] using he)
    have := congrArg Fin.val he'
    rw [hv,Fin.val_zero] at this
    omega
  have hdv : d ≠ u+1 := by
    intro he
    have he' := add_left_cancel he
    have := congrArg Fin.val he'
    rw [hv,hv1] at this
    omega
  have hpu : p u=r-(u+1) := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_right] using hp (u+1)
  have hpv : p (u+1)=r-u := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left] using hp u
  have hother (j : Fin n) (hju : j ≠ u) (hjv : j ≠ u+1) : p j=r-j := by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hju hjv] using hp j
  have hdouble : ((m+1 : ℕ) : Fin n)+((m+1 : ℕ) : Fin n)=1 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Fin.natCast_self] at he
    simp only [Nat.cast_add,Nat.cast_one]
    linear_combination -he
  have hdRaw : p d-d=p u-u := by
    rw [hother d hdu hdv,hpu]
    dsimp only [d]
    linear_combination -hdouble
  constructor
  · intro hi
    by_cases hiu : i=u
    · exact Or.inl hiu
    by_cases hiv : i=u+1
    · exact Or.inr (Or.inl hiv)
    apply Or.inr
    apply Or.inr
    have hc := reflection_complete_odd (p*Equiv.swap u (u+1)) r hp m hn
    change i=d
    apply hc
    have he := hi.trans hdRaw.symm
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hiu hiv,
      Equiv.swap_apply_of_ne_of_ne hdu hdv] using he
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [hpu,hpv]
      ring
    · exact hdRaw

#print axioms odd_reflection_neighbor_fiber
end LX.AnchoredPhases
