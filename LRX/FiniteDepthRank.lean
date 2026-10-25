import LRX.FiniteWindowInversions
import LRX.FiniteWindowLoad
import LRX.FiniteWindowSupport
import LRX.PacketCycleBudget
import Mathlib

namespace LRX.FiniteWindow
variable {n b : ℕ}

/-- Extending a permutation by fixed positions preserves its nontrivial cycle count. -/
theorem permutation_cycle_count (W : Window n b) (p : State b) :
    (permutation W p).cycleFactorsFinset.card = p.cycleFactorsFinset.card := by
  classical
  have h := congrArg Multiset.card (Equiv.Perm.cycleType_extendDomain (g := p) (windowEquiv W))
  simpa [Equiv.Perm.cycleType, permutation] using h

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- A finite depth inequality for every permutation, without a shortness
hypothesis. Padding is used only inside the proof of the event bound. -/
theorem finite_depth_rank (p : State n) :
    (inversionNumber p : ℤ)+(p.support.card : ℤ) ≤
      (∑ i : Fin n, |displacement p i|)+(p.cycleFactorsFinset.card : ℤ) := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q : State (2*n+1) := FiniteWindow.permutation W p
  have hshort (j : Fin (2*n+1)) : 2*|displacement q j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q,FiniteWindow.displacement_embed]
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hp0 : (0 : ℤ) ≤ p i := by positivity
      have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
      have hpn : (p i : ℤ) < n := by exact_mod_cast (p i).isLt
      have hh : |displacement p i| < (n : ℤ) := by
        unfold displacement
        rw [abs_lt]
        constructor <;> omega
      push_cast
      omega
    · simp only [q,FiniteWindow.displacement_outside W p j hj,abs_zero,mul_zero]
      positivity
  have hr := ZeroGap.reflection_rank_inversion_bound (canonical_lift q) hshort
  have hend : (fun i : Fin (2*n+1) => (i : ℤ)+displacement q i)=(fun i => (q i : ℤ)) := by
    funext i
    unfold displacement
    omega
  change ((q⁻¹).support.card : ℤ)+(LiftedModel.inversionCount (fun i => (i : ℤ)+displacement q i) : ℤ) ≤
    (∑ i, |displacement q i|)+(q.cycleFactorsFinset.card : ℤ) at hr
  rw [Equiv.Perm.support_inv,hend,canonical_inversion_count] at hr
  have hI := FiniteWindow.inversion_number_window W p
  have hs := FiniteWindow.permutation_support_card W p
  have hm := FiniteWindow.displacement_mass W p
  change inversionNumber q=inversionNumber p at hI
  change q.support.card=p.support.card at hs
  change (∑ i, |displacement q i|)=(∑ i, |displacement p i|) at hm
  have hc := FiniteWindow.permutation_cycle_count W p
  change q.cycleFactorsFinset.card=p.cycleFactorsFinset.card at hc
  rw [hI,hs,hm,hc] at hr
  simpa only [add_comm] using hr

#print axioms finite_depth_rank
end LRX.FiniteCuts
