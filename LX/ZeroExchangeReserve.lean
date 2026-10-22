import LX.ReflectionPhases

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

/-- The zero-reserve case is paid for all n, with no reflection hypothesis
left on the input permutation. -/
theorem zero_exchange_reserve_word {p : State n} {a : Fin n}
    (hn : 4 ≤ n) (ha : GlobalMinimum p a)
    (heq : (inversions (displacement p a) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨r,hr⟩ := zero_exchange_reserve_reflection ha heq
  exact reflection_upper_word hn p r hr

/-- Together with the large-reserve payment this leaves a positive, linearly
bounded reserve. This is a necessary condition, not a complete solution. -/
theorem unpaid_positive_exchange_reserve {p : State n} {a : Fin n}
    (hn : 4 ≤ n) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (inversions (displacement p a) : ℤ)<
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
  have hm := global_minimum_majorized ha
  have hshort (i : Fin n) : 2*|displacement p a i| < (n : ℤ) := by
    have hh := short_coordinates (is_lift p a).1 hm i
    by_cases hi : 0 ≤ displacement p a i
    · rw [abs_of_nonneg hi]; omega
    · rw [abs_of_neg (by omega : displacement p a i < 0)]; omega
  have hcap := LRX.FiniteCuts.strict_band_inversion_capacity (is_lift p a) hshort
  change (inversions (displacement p a) : ℤ) ≤ _ at hcap
  have hne : (inversions (displacement p a) : ℤ) ≠
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
    intro heq
    exact hunpaid (zero_exchange_reserve_word hn ha heq)
  omega

#print axioms majorized_capacity_reflection
#print axioms zero_exchange_reserve_reflection
#print axioms zero_exchange_reserve_word
#print axioms unpaid_positive_exchange_reserve
end LX.AnchoredPhases
