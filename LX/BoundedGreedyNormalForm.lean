import LX.GreedyPriceCharacterization
import LX.ShortestLiftRange
import Mathlib

namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A shortest greedy representative exists with finite phase and all
integer displacements strictly between -n and n. The bound comes from
deleting repeated finite label pairs, not an energy-minimality assumption. -/
theorem exists_shortest_bounded_greedy_word (hn : 2 ≤ n) (p : State n) :
    ∃ c : Fin n,∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift p (c : ℤ) d ∧ (∀ i,|d i| ≤ (n : ℤ)-1) ∧ ScanTrace d g ∧
      eval (paidWord c g)=p ∧ (paidWord c g).length=length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  obtain ⟨d,hd,hzero⟩ := exists_exact_word_board hn w
  have hpos := LiftedScan.exact_positions_of_zero hn d w hzero
  have hbound (i : Fin n) : |d i| ≤ (n : ℤ)-1 := by
    have hh := FinitePairReduction.shortest_displacement_bound hn w (by rw [hw]; exact hlen) i
    rw [hpos i,add_sub_cancel_left] at hh
    exact hh
  rw [hw] at hd
  let c : Fin n := (w.count .l : Fin n)
  have hdc : IsLift p (c : ℤ) d := by
    have hh := normalize_phase hd
    change IsLift p (((w.count .l : ℤ) : Fin n) : ℤ) d at hh
    simpa only [c,Int.cast_natCast] using hh
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels,Int.cast_natCast,Fin.cast_val_eq_self] using lift_residue hdc i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  obtain ⟨g,hg⟩ := exists_scan_trace hn d hd.1 hi
  have he : eval (paidWord c g)=p := by
    simpa only [Fin.cast_val_eq_self] using (greedy_lift_price_realized hn p c.val d hdc g hg).1
  have hupper : (paidWord c g).length ≤ w.length :=
    hg.paid_length_le_any_word hn hd.1 hi w hzero
  have hlower := length_le_word (n := n) (paidWord c g)
  rw [he] at hlower
  refine ⟨c,?_⟩
  refine ⟨d,?_⟩
  refine ⟨g,hdc,hbound,hg,he,?_⟩
  exact Nat.le_antisymm (hupper.trans_eq hlen) hlower

theorem length_lower_iff_bounded_greedy_prices (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : Fin n) (d : Fin n → ℤ) (g : List Letter),
      IsLift p (c : ℤ) d → (∀ i,|d i| ≤ (n : ℤ)-1) → ScanTrace d g →
        B ≤ inversions d+paidRotations c g := by
  constructor
  · intro hB c d g hd _ hg
    have hh := (length_lower_iff_greedy_prices hn p B).mp hB c.val d g hd hg
    simpa only [Fin.cast_val_eq_self] using hh
  · intro h
    obtain ⟨c,d,g,hd,hbound,hg,_,hlen⟩ := exists_shortest_bounded_greedy_word hn p
    have hb := h c d g hd hbound hg
    have hp : (paidWord c g).length=inversions d+paidRotations c g := by
      simpa only [Fin.cast_val_eq_self] using (greedy_lift_price_realized hn p c.val d hd g hg).2
    omega

#print axioms exists_shortest_bounded_greedy_word
#print axioms length_lower_iff_bounded_greedy_prices
end LX
