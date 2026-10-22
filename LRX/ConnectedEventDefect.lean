import LRX.SpanningEventSublist
import LRX.MinimalEventCycle
import LRX.EventSublistRankBound
import LRX.FiniteCutLoad

namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The strong connected-event inequality, with its spanning cycle extracted internally. -/
theorem connected_event_defect (events : List (Event n)) (p : State n) (root : Fin n)
    (hprod : (events.map eventSwap).prod=p)
    (hcarrier : eventComponent events root=p.support) (hsize : 2 ≤ p.support.card) :
    2*((p.cycleFactorsFinset.card : ℤ)-1) ≤
      (events.length : ℤ)-(p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  obtain ⟨part,hpart,hcomp,hlen,_,_⟩ := component_spanning_event_sublist events root
  have hmin : part.length+1=(eventComponent part root).card := by rw [hcomp]; exact hlen
  have hc : 2 ≤ (eventComponent part root).card := by rw [hcomp,hcarrier]; exact hsize
  obtain ⟨hcycle,hsupport⟩ := minimal_event_product_cycle part root hmin hc
  rw [hcomp,hcarrier] at hsupport
  rw [hcarrier] at hlen
  exact spanning_cycle_event_defect hpart p (part.map eventSwap).prod hprod rfl hcycle hsupport hlen

/-- D2 for an actual short canonical root packet: all moving positions are in its core.
No event list, spanning tree, cycle factorization or defect bound is supplied. -/
theorem canonical_packet_strong_defect (p : State n)
    (hshort : ∀ i, 2*|FiniteCuts.displacement p.symm i| < (n : ℤ)) (root : Fin n)
    (hroot : root ∈ p.support)
    (hpacket : ∀ i ∈ p.support, PrunedLift.InCore p (FiniteCuts.displacement p.symm) root i) :
    2*((p.cycleFactorsFinset.card : ℤ)-1) ≤
      (∑ i, |FiniteCuts.displacement p.symm i|)-
        (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
        (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  classical
  have hd : AffineLift.IsLift p 0 (FiniteCuts.displacement p.symm) := by
    simpa only [Equiv.symm_symm] using FiniteCuts.canonical_lift p.symm
  obtain ⟨events,hprod,hlen,_,hactive,hsep,_,htravel⟩ := sorting_events hd hshort
  have hmove (i : Fin n) (hi : FiniteCuts.displacement p.symm i ≠ 0) : i ∈ p.support := by
    apply Equiv.Perm.mem_support.mpr
    intro hf
    have hinv : p.symm i=i := by
      apply p.injective
      simpa only [Equiv.apply_symm_apply] using hf.symm
    exact hi (by simp only [FiniteCuts.displacement,hinv,sub_self])
  have hcarrier : eventComponent events root=p.support := by
    ext i
    constructor
    · intro hi
      have hp := (mem_eventComponent _ _ _).mp hi
      induction hp with
      | refl => exact hroot
      | @tail u v hp he ih =>
        obtain ⟨e,he,⟨hu,hv⟩ | ⟨hu,hv⟩⟩ := he
        · exact hv ▸ hmove e.2 (hactive e he).2
        · exact hv ▸ hmove e.1 (hactive e he).1
    · intro hi
      exact (mem_eventComponent _ _ _).mpr (core_event_reachable hprod hsep htravel (hpacket i hi))
  have hsize : 2 ≤ p.support.card := Equiv.Perm.two_le_card_support_of_ne_one (by
    intro hp
    have hm := Equiv.Perm.mem_support.mp hroot
    exact hm (by rw [hp]; rfl))
  have hh := connected_event_defect events p root hprod hcarrier hsize
  have hF : (fun i : Fin n => (i : ℤ)+FiniteCuts.displacement p.symm i) =
      (fun i : Fin n => (p.symm i : ℤ)) := by
    funext i
    simp [FiniteCuts.displacement]
  rw [hF] at hlen
  rw [hlen] at hh
  exact hh

#print axioms connected_event_defect
#print axioms canonical_packet_strong_defect
end LRX.ZeroGap
