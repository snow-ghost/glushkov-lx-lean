import LRX.FiniteWindowInversions
import LRX.FiniteWindowSupport

namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Every canonical finite shallow cycle has an arrow between neighboring
support ranks. Padding removes the shortness premise of the event proof. -/
theorem shallow_cycle_rank_neighbor {p : State n} (hp : p.IsCycle)
    (hshallow : (∑ i : Fin n, |FiniteCuts.displacement p.symm i|)=
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)+
        (p.support.card : ℤ)-1) :
    ∃ x y, RankAdjacent p.support x y ∧ p x=y := by
  classical
  letI : NeZero (2*n+1) := ⟨by omega⟩
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q : State (2*n+1) := FiniteWindow.permutation W p
  have hq : q.IsCycle := FiniteWindow.permutation_is_cycle W p hp
  have hshort (j : Fin (2*n+1)) : 2*|FiniteCuts.displacement q.symm j| < (2*n+1 : ℕ) := by
    by_cases hj : FiniteWindow.Contains W j
    · obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hj
      simp only [q,FiniteWindow.permutation_symm,FiniteWindow.displacement_embed]
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have hp0 : (0 : ℤ) ≤ p.symm i := by positivity
      have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
      have hpn : (p.symm i : ℤ) < n := by exact_mod_cast (p.symm i).isLt
      have hd : |FiniteCuts.displacement p.symm i| < (n : ℤ) := by
        unfold FiniteCuts.displacement
        rw [abs_lt]
        constructor <;> omega
      push_cast
      omega
    · simp only [q,FiniteWindow.permutation_symm,FiniteWindow.displacement_outside W p.symm j hj,abs_zero,mul_zero]
      positivity
  have hI : LiftedModel.inversionCount (fun j : Fin (2*n+1) => (q.symm j : ℤ))=
      LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) := by
    rw [FiniteCuts.canonical_inversion_count,FiniteCuts.canonical_inversion_count]
    exact FiniteWindow.inversion_number_window W p.symm
  have hs : q.support.card=p.support.card := FiniteWindow.permutation_support_card W p
  have hmass : (∑ j : Fin (2*n+1), |FiniteCuts.displacement q.symm j|)=
      ∑ i : Fin n, |FiniteCuts.displacement p.symm i| := FiniteWindow.displacement_mass W p.symm
  have hz : (∑ j : Fin (2*n+1), |FiniteCuts.displacement q.symm j|)=
      (LiftedModel.inversionCount (fun j : Fin (2*n+1) => (q.symm j : ℤ)) : ℤ)+
        (q.support.card : ℤ)-1 := by rw [hmass,hI,hs]; exact hshallow
  exact FiniteWindow.neighbor_pullback W p (short_shallow_cycle_neighbor hq hshort hz)

#print axioms shallow_cycle_rank_neighbor
end LRX.ZeroGap
