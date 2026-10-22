import LRX.CanonicalCycleEvents
import LRX.FiniteCutLoad

namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The needed rank-neighbor consequence for a canonical shallow cycle
whose displacements satisfy the existing sorting trace's shortness bound.
The proof uses the actual event tree, not separable-permutation theory. -/
theorem short_shallow_cycle_neighbor {p : State n} (hp : p.IsCycle)
    (hshort : ∀ i, 2*|FiniteCuts.displacement p.symm i| < (n : ℤ))
    (hshallow : (∑ i : Fin n, |FiniteCuts.displacement p.symm i|)=
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)+
        (p.support.card : ℤ)-1) :
    ∃ x y, RankAdjacent p.support x y ∧ p x=y := by
  classical
  have hd : AffineLift.IsLift p 0 (FiniteCuts.displacement p.symm) := by
    simpa only [Equiv.symm_symm] using FiniteCuts.canonical_lift p.symm
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,_,htravel⟩ := sorting_events hd hshort
  have hF : (fun i : Fin n => (i : ℤ)+FiniteCuts.displacement p.symm i)=
      (fun i : Fin n => (p.symm i : ℤ)) := by
    funext i
    simp [FiniteCuts.displacement]
  rw [hF] at hlen
  have hcount : events.length+1=p.support.card := by omega
  have ha : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support := by
    have active (i : Fin n) (hi : FiniteCuts.displacement p.symm i ≠ 0) : i ∈ p.support := by
      have hne : p.symm i ≠ i := by
        intro h
        apply hi
        simp [FiniteCuts.displacement,h]
      have hm : i ∈ p⁻¹.support := Equiv.Perm.mem_support.mpr hne
      simpa only [Equiv.Perm.support_inv] using hm
    intro e he
    exact ⟨active e.1 (hactive e he).1,active e.2 (hactive e he).2⟩
  have ht : ∀ i, Travel events i (p.symm i) ((p.symm i : ℤ)-(i : ℤ)) := htravel
  have hlinear := canonical_cycle_events_linear hp events hprod ha hcount hneq ht
  exact cycle_neighbor_of_events hp events hprod ha hcount hlinear hsep

#print axioms short_shallow_cycle_neighbor
end LRX.ZeroGap
