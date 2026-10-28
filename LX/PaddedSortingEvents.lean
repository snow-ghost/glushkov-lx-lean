import LX.FiniteInversionDecomposition
import LX.FiniteWindowLoad
import LX.ShallowContraction
import LX.ZeroGapEvents
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- An actual separated linear sorting trace for every finite permutation,
obtained by padding with fixed positions. -/
theorem padded_sorting_events (p : State n) :
    let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
    let q := FiniteWindow.permutation W p
    ∃ events : List (ZeroGap.Event (2*n+1)),
      (events.map ZeroGap.eventSwap).prod=q ∧
      (events.length : ℤ)=(∑ i, |displacement p i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧
      (∀ e ∈ events, e.1 ∈ q.support ∧ e.2 ∈ q.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise ZeroGap.LaterOutside := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q := FiniteWindow.permutation W p
  have hshort (j : Fin (2*n+1)) : 2*|displacement q.symm j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q,FiniteWindow.permutation_symm,FiniteWindow.displacement_embed]
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hp0 : (0 : ℤ) ≤ p.symm i := by positivity
      have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
      have hpn : (p.symm i : ℤ) < n := by exact_mod_cast (p.symm i).isLt
      have hh : |displacement p.symm i| < (n : ℤ) := by
        unfold displacement
        rw [abs_lt]
        constructor <;> omega
      push_cast
      omega
    · simp only [q,FiniteWindow.permutation_symm,
        FiniteWindow.displacement_outside W p.symm j hj,abs_zero,mul_zero]
      positivity
  have hd : AffineLift.IsLift q 0 (displacement q.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift q.symm
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,_⟩ := ZeroGap.sorting_events hd hshort
  have hF : (fun j : Fin (2*n+1) => (j : ℤ)+displacement q.symm j)=
      (fun j => (q.symm j : ℤ)) := by funext j; unfold displacement; omega
  rw [hF,canonical_inversion_count] at hlen
  have hInv : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  rw [hInv,displacement_mass_inverse] at hlen
  have hmass : (∑ j, |displacement q j|)=∑ i, |displacement p i| := FiniteWindow.displacement_mass W p
  have hI : inversionNumber q=inversionNumber p := FiniteWindow.inversion_number_window W p
  have hcontains (j : Fin (2*n+1)) (hj : j ∈ q.support) : FiniteWindow.Contains W j := by
    by_contra hh
    exact (Equiv.Perm.mem_support.mp hj) (FiniteWindow.permutation_outside W p j hh)
  have ha : ∀ e ∈ events, e.1 ∈ q.support ∧ e.2 ∈ q.support := by
    have hm (j : Fin (2*n+1)) (hj : displacement q.symm j ≠ 0) : j ∈ q.support := by
      have hne : q.symm j ≠ j := by
        intro hh
        exact hj (by simp only [displacement,hh,sub_self])
      have hh : j ∈ (q⁻¹).support := Equiv.Perm.mem_support.mpr hne
      simpa only [Equiv.Perm.support_inv] using hh
    intro e he
    exact ⟨hm e.1 (hactive e he).1,hm e.2 (hactive e he).2⟩
  have hlinear : ∀ e ∈ events, e.1.val < e.2.val := by
    intro e he
    have h0 := hcontains e.1 (ha e he).1
    have h1 := hcontains e.2 (ha e he).2
    change 0 ≤ e.1.val ∧ e.1.val < 0+n at h0
    change 0 ≤ e.2.val ∧ e.2.val < 0+n at h1
    have hne := hneq e he
    have hsmall' := hsmall e he
    by_contra hh
    have hne' : e.1.val ≠ e.2.val := fun h => hne (Fin.ext h)
    have hrev : e.2 < e.1 := by change e.2.val < e.1.val; omega
    unfold ZeroGap.distance at hsmall'
    rw [Fin.coe_sub_iff_lt.mpr hrev] at hsmall'
    omega
  rw [hmass,hI] at hlen
  exact ⟨events,hprod,hlen,hneq,ha,hlinear,hsep⟩

#print axioms padded_sorting_events
end LX.Core.FiniteCuts
