import LRX.SourcePacketEventCover

namespace LRX.FiniteCuts
open FiniteWindow RotationWords ZeroGap
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- Every actual filling cycle contributes at least one to its half-peak sum. -/
theorem filling_half_peak_sum_ge_count (p : State n) :
    ((fillingCycles p).card : ℤ) ≤ fillingHalfPeakSum p := by
  have bound : ∀ xs : List (State n), (∀ q ∈ xs, 1 ≤ leftPeak q n) →
      (xs.length : ℤ) ≤ (xs.map (fun q => (leftPeak q n : ℤ))).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons q xs ih =>
      intro hx
      have hq := hx q (by simp)
      have ht := ih (fun r hr => hx r (by simp [hr]))
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons]
      omega
  have h := bound (fillingCycles p).toList (by
    intro q hq
    have hfactor := (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).1
    have hcy := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hfactor).1
    obtain ⟨i,hi⟩ := hcy.nonempty_support
    exact moved_global_peak_positive q i (Equiv.Perm.mem_support.mp hi))
  simpa only [Finset.length_toList,fillingHalfPeakSum] using h

/-- The weak aggregate defect needed by first C8, obtained directly from the
actual sorting-event cover. No component-defect additivity is assumed. -/
theorem aggregate_source_filling_defect (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) :
    -((componentRoots p).card : ℤ) ≤
      (∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ)-
        (p.support.card : ℤ)+fillingHalfPeakSum p := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,_,hsep,_,htravel⟩ := sorting_events hd (majorized_short hd hmaj)
  have hc := source_packet_event_cover hn p hm events hprod hsep htravel
  have hc' : (p.support.card : ℤ) ≤ (events.length : ℤ)+
      ((componentRoots p).card : ℤ)+((fillingCycles p).card : ℤ) := by exact_mod_cast hc
  have hF : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=
      (fun i : Fin n => (p.symm i : ℤ)) := by
    funext i
    simp [displacement]
  rw [hF,canonical_inversion_count] at hlen
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hI] at hlen
  have hS := filling_half_peak_sum_ge_count p
  linarith

/-- First C8 for the original routed map, derived from the weak aggregate
defect of its sorting graph and the actual filling peaks. -/
theorem peak_activity_bound (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+(k : ℤ)-
      (sourceHalfPeak p : ℤ)-(2*eps+(n%2 : ℕ)-((n-p.support.card : ℕ) : ℤ)) := by
  have hdef := aggregate_source_filling_defect hn p hmaj (by omega)
  rw [hc,Nat.cast_add,Nat.cast_one] at hdef
  have hN := choose_two_half_identity n
  have hn' : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hf : ((n-p.support.card : ℕ) : ℤ)=(n : ℤ)-(p.support.card : ℤ) := by omega
  dsimp only
  rw [hf]
  unfold peakExcess
  linarith

#print axioms filling_half_peak_sum_ge_count
#print axioms aggregate_source_filling_defect
#print axioms peak_activity_bound
end LRX.FiniteCuts
