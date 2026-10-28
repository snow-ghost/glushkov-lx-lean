import LX.GreedyWordNormalForm
import Mathlib

namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every balanced lift's greedy price is the length of a literal word
with the specified endpoint, including its final orientation. -/
theorem greedy_lift_price_realized (hn : 2 ≤ n) (p : State n) (c : ℕ)
    (d : Fin n → ℤ) (hd : IsLift p (c : ℤ) d) (g : List Letter) (hg : ScanTrace d g) :
    eval (paidWord (c : Fin n) g)=p ∧
      (paidWord (c : Fin n) g).length=inversions d+paidRotations (c : Fin n) g := by
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels,Int.cast_natCast] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  have hs := sorting_word_of_zero hn p.symm (c : Fin n) d hl g hg.run_zero
  have he : p⁻¹*eval (paidWord (c : Fin n) g)=1 := by
    simpa only [paidWord,Equiv.Perm.inv_def] using hs
  exact ⟨(inv_mul_eq_one.mp he).symm,hg.paid_length hn hd.1 hi _⟩

/-- Exact lower-bound reduction: it is necessary and sufficient to bound
all balanced-lift greedy prices. Restricting to anchor lifts, minimum
energy lifts or minimum height lifts would require another theorem. -/
theorem length_lower_iff_greedy_prices (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : ℕ) (d : Fin n → ℤ) (g : List Letter),
      IsLift p (c : ℤ) d → ScanTrace d g →
        B ≤ inversions d+paidRotations (c : Fin n) g := by
  constructor
  · intro hB c d g hd hg
    obtain ⟨he,hprice⟩ := greedy_lift_price_realized hn p c d hd g hg
    have hlo := length_le_word (n := n) (paidWord (c : Fin n) g)
    rw [he,hprice] at hlo
    exact hB.trans hlo
  · intro h
    obtain ⟨c,d,g,hd,hg,_,hlen⟩ := exists_shortest_greedy_word hn p
    have hb := h c d g hd hg
    have hp := (greedy_lift_price_realized hn p c d hd g hg).2
    omega

#print axioms greedy_lift_price_realized
#print axioms length_lower_iff_greedy_prices
end LX
