import LX.BinaryLiftSelection

namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The shortest-word search is finite in the phase and lift selection.
The subsequent scan is unique. No energy-based pruning is assumed. -/
theorem exists_shortest_selected_greedy_word (hn : 2 ≤ n) (p : State n) :
    ∃ c : Fin n,∃ S : Finset (Fin n),∃ g : List Letter,
      BinaryLift.ValidSelection p c S ∧ ScanTrace (BinaryLift.displacement p c S) g ∧
      eval (paidWord c g)=p ∧ (paidWord c g).length=length p := by
  obtain ⟨c,d,g,hd,hbound,hg,he,hlen⟩ := exists_shortest_bounded_greedy_word hn p
  obtain ⟨S,hS,hSd⟩ := BinaryLift.bounded_lift_selection p c d hd hbound
  refine ⟨c,?_⟩
  refine ⟨S,?_⟩
  refine ⟨g,hS,?_,he,hlen⟩
  simpa only [hSd] using hg

theorem length_lower_iff_selected_greedy_prices (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : Fin n) (S : Finset (Fin n)) (g : List Letter),
      BinaryLift.ValidSelection p c S → ScanTrace (BinaryLift.displacement p c S) g →
        B ≤ inversions (BinaryLift.displacement p c S)+paidRotations c g := by
  constructor
  · intro hB c S g hS hg
    have hd := BinaryLift.selected_lift p c S hS
    have hb := (length_lower_iff_greedy_prices hn p B).mp hB c.val _ g hd hg
    simpa only [Fin.cast_val_eq_self] using hb
  · intro h
    obtain ⟨c,S,g,hS,hg,_,hlen⟩ := exists_shortest_selected_greedy_word hn p
    have hb := h c S g hS hg
    have hd := BinaryLift.selected_lift p c S hS
    have hp : (paidWord c g).length=inversions (BinaryLift.displacement p c S)+paidRotations c g := by
      simpa only [Fin.cast_val_eq_self] using (greedy_lift_price_realized hn p c.val _ hd g hg).2
    omega

#print axioms exists_shortest_selected_greedy_word
#print axioms length_lower_iff_selected_greedy_prices
end LX
