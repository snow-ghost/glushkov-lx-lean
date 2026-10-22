import LX.TwoColorPairs
import LRX.FiniteWindowInversions

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Winding parity forces a crossing for every unreversed pair of equal
color. A finite perturbation of the reflection can lose only its own
finite inversion count. No minimum-energy hypothesis is used. -/
theorem reflection_perturbation_pairs (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    sameColorPairs (fun i => decide (k i % 2=0)) ≤
      inversions d+LRX.FiniteCuts.inversionNumber ρ := by
  let χ : Fin n → Bool := fun i => decide (k i % 2=0)
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hp (i j : Fin n) : (if i < j ∧ χ i=χ j then 1 else 0) ≤
      (if i < j then ((targets d j-targets d i)/(n : ℤ)).natAbs else 0)+
      (if i.val < j.val ∧ (ρ j).val < (ρ i).val then 1 else 0 : ℕ) := by
    by_cases hpair : i < j ∧ χ i=χ j
    · rw [ite_eq_left hpair,ite_eq_left hpair.1]
      by_cases hr : (ρ j).val < (ρ i).val
      · rw [ite_eq_left ⟨hpair.1,hr⟩]; omega
      · rw [ite_eq_right (by omega : ¬(i.val < j.val ∧ (ρ j).val < (ρ i).val)),add_zero]
        have hne : ρ i ≠ ρ j := fun hh => (ne_of_lt hpair.1) (ρ.injective hh)
        have hlt : (ρ i : ℤ) < ρ j := by
          have hvals : (ρ i).val ≠ (ρ j).val := fun hh => hne (Fin.ext hh)
          omega
        have hq : (targets d j-targets d i)/(n : ℤ)=k j-k i-1 := by
          rw [hF j,hF i]
          apply LRX.PeriodicBuffer.quotient_eq_of_bounds hn
          · have hi := (ρ i).isLt
            have hj := (ρ j).isLt
            nlinarith
          · nlinarith
        have hcolor : (k i % 2=0) ↔ (k j % 2=0) := by
          simpa only [χ,decide_eq_decide] using hpair.2
        have hmod : k i % 2=k j % 2 := by omega
        have hne0 : k j-k i-1 ≠ 0 := by omega
        rw [hq]
        exact Int.natAbs_pos.mpr hne0
    · rw [ite_eq_right hpair]; exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))
  simpa only [Finset.sum_add_distrib,sameColorPairs,inversions,LRX.LiftedModel.inversionCount,
    LRX.FiniteCuts.inversionNumber,χ] using hs

theorem even_reflection_lift_inversions_lower (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ) (m : ℕ) (hn : n=2*m)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    m*(m-1) ≤ inversions d+LRX.FiniteCuts.inversionNumber ρ :=
  (even_same_color_pairs_lower _ m hn).trans (reflection_perturbation_pairs d ρ C k hF)

theorem odd_reflection_lift_inversions_lower (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ) (m : ℕ) (hn : n=2*m+1)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    m^2 ≤ inversions d+LRX.FiniteCuts.inversionNumber ρ :=
  (odd_same_color_pairs_lower _ m hn).trans (reflection_perturbation_pairs d ρ C k hF)

/-- The winding data are extracted from an actual lift of the target;
they are not an extra premise in the lower bound. -/
theorem exists_reflection_winding {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (ρ : State n)
    (hp : ∀ i,p.symm i=1-ρ i) :
    ∃ k : Fin n → ℤ,∀ i,targets d i=(c+1)-(ρ i : ℤ)+(n : ℤ)*k i := by
  have hi (i : Fin n) : ∃ k : ℤ,targets d i=(c+1)-(ρ i : ℤ)+(n : ℤ)*k := by
    have hc : (((c+1)-(ρ i : ℤ) : ℤ) : Fin n)=(targets d i : Fin n) := by
      have hh := LRX.AffineLift.lift_residue hd i
      rw [hp] at hh
      simp only [targets,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_natCast,
        Fin.cast_val_eq_self] at hh ⊢
      linear_combination -hh
    have hmod := (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp hc
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hmod
    exact ⟨k,by omega⟩
  choose k hk using hi
  exact ⟨k,hk⟩

theorem even_reflection_lift_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (ρ : State n)
    (hp : ∀ i,p.symm i=1-ρ i) (m : ℕ) (hn : n=2*m) :
    m*(m-1) ≤ inversions d+LRX.FiniteCuts.inversionNumber ρ := by
  obtain ⟨k,hk⟩ := exists_reflection_winding hd ρ hp
  exact even_reflection_lift_inversions_lower d ρ (c+1) k m hn hk

theorem odd_reflection_lift_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (ρ : State n)
    (hp : ∀ i,p.symm i=1-ρ i) (m : ℕ) (hn : n=2*m+1) :
    m^2 ≤ inversions d+LRX.FiniteCuts.inversionNumber ρ := by
  obtain ⟨k,hk⟩ := exists_reflection_winding hd ρ hp
  exact odd_reflection_lift_inversions_lower d ρ (c+1) k m hn hk

#print axioms even_reflection_lift_inversions_lower
#print axioms odd_reflection_lift_inversions_lower
#print axioms even_reflection_lift_lower
#print axioms odd_reflection_lift_lower
end LX.AffineScan
