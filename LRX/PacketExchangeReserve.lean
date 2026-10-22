import LRX.ZeroGapComponentCounting
import LRX.ExchangeReserveNonnegative

/-! The source-packet exchange reserve follows from the actual sorting
component, its edge count, and the majorized active-set energy bound. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem activity_core_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) (root : Fin n) :
    (p.support.card : ℤ)+((PrunedLift.core p d root).card : ℤ)+
      2*(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      2*(∑ i : Fin n, |d i|)+2 := by
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,htravel⟩ := sorting_events hd hshort
  have hsub : PrunedLift.core p d root ⊆ eventComponent events root := by
    intro i hi
    exact (mem_eventComponent events root i).mpr
      (core_event_reachable hprod hsep htravel ((PrunedLift.mem_core p d root i).mp hi))
  have hcard := Finset.card_le_card hsub
  have hcount := support_component_count events root
  rw [hprod] at hcount
  omega

theorem core_exchange_reserve {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root : Fin n) :
    ((PrunedLift.core p d root).card/2 : ℕ)- (1 : ℤ) ≤ FiniteGaps.exchangeReserve d := by
  have hmass := active_mass_cap hd hm
  have hactivity := activity_core_inversion_bound hd (FiniteWindow.majorized_short hd hm) root
  have hhalf : 2*(p.support.card/2) ≤ p.support.card := by omega
  have hcore : 2*((PrunedLift.core p d root).card/2) ≤ (PrunedLift.core p d root).card := by omega
  have hC : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      ((PrunedLift.core p d root).card/2 : ℕ)-1 ≤
      (p.support.card/2 : ℕ)*((n : ℤ)-(p.support.card/2 : ℕ))-(p.support.card/2 : ℕ) := by omega
  have hquad : 4*((LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      ((PrunedLift.core p d root).card/2 : ℕ)-1) ≤ ((n : ℤ)-1)^2 := by
    nlinarith [sq_nonneg ((n : ℤ)-1-2*(p.support.card/2 : ℕ))]
  have hQ := FiniteGaps.floor_square_identity n
  have hn : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have hbound : -1 ≤ 4*(FiniteGaps.exchangeReserve d-
      (((PrunedLift.core p d root).card/2 : ℕ)- (1 : ℤ))) := by
    unfold FiniteGaps.exchangeReserve
    nlinarith
  omega

theorem packet_exchange_reserve {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    (PrunedLift.coreHalfSize p d : ℤ)-1 ≤ FiniteGaps.exchangeReserve d :=
  core_exchange_reserve hd hm 0

#print axioms activity_core_inversion_bound
#print axioms packet_exchange_reserve
end LRX.ZeroGap

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The first internal-gap routing case, with its exchange reserve proved
from the input lift rather than supplied as a hypothesis. -/
theorem first_internal_gap_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hinternal : Internal p d 0)
    (start finish : Fin n) (hxy : start.val ≤ finish.val)
    (hy : finish.val ≤ size (PrunedLift.core p d 0) 0) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 :=
  first_internal_gap_sharp_word hn hd hm hroot hcover hinternal
    (ZeroGap.packet_exchange_reserve hd hm) start finish hxy hy

#print axioms first_internal_gap_word
end LRX.FiniteGaps
