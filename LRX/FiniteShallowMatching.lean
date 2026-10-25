import LRX.FiniteInversionDecomposition
import LRX.MatchingEventsNoncrossing
import LRX.ShallowContraction
import LRX.StrictBandEqualityPairs
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- A finite permutation attaining the support half-rank depth bound has no
alternating pairs. The proof uses real sorting events in a padded window. -/
theorem finite_shallow_matching_noncrossing (p : State n) (k : ℕ)
    (hsupport : p.support.card=2*k)
    (hdef : (∑ i, |displacement p i|)-(inversionNumber p : ℤ)=(k : ℤ))
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : p a=c) : p b ≠ d := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q := FiniteWindow.permutation W p
  have hshort (j : Fin (2*n+1)) : 2*|displacement q.symm j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q, FiniteWindow.permutation_symm, FiniteWindow.displacement_embed]
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
    · simp only [q, FiniteWindow.permutation_symm,
        FiniteWindow.displacement_outside W p.symm j hj, abs_zero, mul_zero]
      positivity
  have hq : AffineLift.IsLift q 0 (displacement q.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift q.symm
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,_⟩ := ZeroGap.sorting_events hq hshort
  have hend : (fun i : Fin (2*n+1) => (i : ℤ)+displacement q.symm i)=
      (fun i => (q.symm i : ℤ)) := by funext i; unfold displacement; omega
  rw [hend, canonical_inversion_count, displacement_mass_inverse] at hlen
  have hInv : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  rw [hInv] at hlen
  have hI := FiniteWindow.inversion_number_window W p
  have hmass := FiniteWindow.displacement_mass W p
  change inversionNumber q=inversionNumber p at hI
  change (∑ i, |displacement q i|)=(∑ i, |displacement p i|) at hmass
  rw [hI,hmass,hdef] at hlen
  have hlength : events.length=k := by exact_mod_cast hlen
  have hcard : (events.map ZeroGap.eventSwap).prod.support.card=2*events.length := by
    rw [hprod,hlength]
    exact (FiniteWindow.permutation_support_card W p).trans hsupport
  have hinside (j : Fin (2*n+1)) (hj : displacement q.symm j ≠ 0) : j.val < n := by
    have hcontains : FiniteWindow.Contains W j := by
      by_contra hn
      apply hj
      exact FiniteWindow.displacement_outside W p.symm j hn
    change 0 ≤ j.val ∧ j.val < 0+n at hcontains
    omega
  have hlinear : ∀ e ∈ events, e.1.val < e.2.val := by
    intro e he
    have h1 := hinside e.1 (hactive e he).1
    have h2 := hinside e.2 (hactive e he).2
    have hn := hneq e he
    have hs := hsmall e he
    by_contra hnot
    have hne : e.1.val ≠ e.2.val := fun hh => hn (Fin.ext hh)
    have hrev : e.2 < e.1 := by change e.2.val < e.1.val; omega
    unfold ZeroGap.distance at hs
    rw [Fin.coe_sub_iff_lt.mpr hrev] at hs
    omega
  have hemb (x y : Fin n) (hxy : x.val < y.val) :
      (FiniteWindow.embed W x).val < (FiniteWindow.embed W y).val := by
    dsimp [FiniteWindow.embed]
    omega
  have hpair : (events.map ZeroGap.eventSwap).prod (FiniteWindow.embed W a)=FiniteWindow.embed W c := by
    rw [hprod]
    change FiniteWindow.permutation W p (FiniteWindow.embed W a)=_
    rw [FiniteWindow.permutation_embed,hac]
  have hn := ZeroGap.maximal_event_pairs_noncrossing events hcard hlinear hsep
    (FiniteWindow.embed W a) (FiniteWindow.embed W b) (FiniteWindow.embed W c) (FiniteWindow.embed W d)
    (hemb a b hab) (hemb b c hbc) (hemb c d hcd) hpair
  intro hbd
  apply hn
  rw [hprod]
  change FiniteWindow.permutation W p (FiniteWindow.embed W b)=_
  rw [FiniteWindow.permutation_embed,hbd]

/-- The equality case of a completion with inherited extremes is noncrossing. -/
theorem inherited_capacity_equality_noncrossing [NeZero n]
    {p : State n} {phase : ℤ} {original disp : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p phase disp) (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hband : ∀ i, 0 ≤ disp i+h ∧ disp i+h < (n : ℤ))
    (hinherit : ∀ i, disp i= -h → original i= -h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+disp i) : ℤ)=
      h*((n : ℤ)-h-1))
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : shiftedLiftPermutation p phase h a=c) : shiftedLiftPermutation p phase h b ≠ d := by
  obtain ⟨hs,hc,hdef,_⟩ := inherited_capacity_equality_pairs horiginal hmaj hd h hh hband hinherit heq
  let q := shiftedLiftPermutation p phase h
  have hsNat : q.support.card=2*q.cycleFactorsFinset.card := by
    have hz : (q.support.card : ℤ)=2*(q.cycleFactorsFinset.card : ℤ) := by
      change (q.support.card : ℤ)=2*h at hs
      change (q.cycleFactorsFinset.card : ℤ)=h at hc
      omega
    exact_mod_cast hz
  have hz : (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=(q.cycleFactorsFinset.card : ℤ) := by
    change (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h at hdef
    change (q.cycleFactorsFinset.card : ℤ)=h at hc
    omega
  exact finite_shallow_matching_noncrossing q q.cycleFactorsFinset.card hsNat hz
    a b c d hab hbc hcd hac

#print axioms finite_shallow_matching_noncrossing
#print axioms inherited_capacity_equality_noncrossing
end LRX.FiniteCuts
