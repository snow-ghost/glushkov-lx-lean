import LRX.ZeroGapCycleRoots
import LRX.ActiveSetSlack

/-! Reflection-rank and packet-cycle bounds come from the actual sorting
events. Combined with majorization they pay the two-arc numerical budget. -/
namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem reflection_rank_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    (p.support.card : ℤ)+(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      (∑ i : Fin n, |d i|)+((p⁻¹).cycleFactorsFinset.card : ℤ) := by
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,htravel⟩ := sorting_events hd hshort
  have h := cycle_root_count hprod
  omega

theorem packet_cycle_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) (root : Fin n) :
    (p.support.card : ℤ)+(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      (∑ i : Fin n, |d i|)+((outsideCycles p d root).card : ℤ)+1 := by
  obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hsmall,htravel⟩ := sorting_events hd hshort
  have h := packet_cycle_root_count hprod hsep htravel root
  omega

#print axioms reflection_rank_inversion_bound
#print axioms packet_cycle_inversion_bound
end LRX.ZeroGap

namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_two_arc_budget {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root : Fin n) :
    (n/2 : ℕ)-((ZeroGap.outsideCycles p d root).card : ℤ)-1 ≤ exchangeReserve d+epsilon d := by
  have hrank := ZeroGap.packet_cycle_inversion_bound hd (FiniteWindow.majorized_short hd hm) root
  have hfixed := fixed_slack_nonneg hd hm
  have hf := fixed_count_identity p
  have hn : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  unfold exchangeReserve epsilon at *
  omega

theorem packet_two_arc_price {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root : Fin n) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      (∑ i : Fin n, |d i|)+(n/2 : ℕ)-((ZeroGap.outsideCycles p d root).card : ℤ)-1 ≤
      (n.choose 2 : ℤ) := by
  have h := packet_two_arc_budget hd hm root
  have hn := quarter_budget (n := n) (NeZero.pos n)
  unfold exchangeReserve epsilon at h
  omega

#print axioms packet_two_arc_budget
#print axioms packet_two_arc_price
end LRX.FiniteGaps
