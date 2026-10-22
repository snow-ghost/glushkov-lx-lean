import LX.GreedyWordNormalForm
import LX.DirectedLowerRegression

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem saturated_sweep_zero_mono (d : Fin n → ℤ) {a b : ℕ} (hab : a ≤ b)
    (ha : ∀ i,saturatedSweep d a i=0) : ∀ i,saturatedSweep d b i=0 := by
  induction b,hab using Nat.le_induction with
  | base => exact ha
  | succ b _ ih =>
    have he : saturatedSweep d b=(fun _ => 0) := funext ih
    rw [saturated_sweep_succ,he]
    intro i
    simp [compareHead,rotate]

/-- A single nonzero entry after t greedy rotations certifies that every
word realizing this exact lift needs strictly more than t rotations. -/
theorem rotations_gt_of_greedy_nonzero (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (t : ℕ) (i : Fin n) (hi : saturatedSweep d t i ≠ 0)
    (w : List Letter) (hw : ∀ j,run w d j=0) : t < w.count .l := by
  by_contra hnot
  have hz := saturated_sweep_zero_of_word hn d w hb hw
  exact hi (saturated_sweep_zero_mono d (by omega) hz i)

end LX.AffineScan

namespace LX.DirectedLowerRegression
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift

theorem trial_greedy_unfinished : saturatedSweep trialDisplacement 6 1 ≠ 0 := by
  decide +kernel

/-- The former false price 12 is eliminated by the proved scheduling
constraint. This statement retains the exact trial lift as a hypothesis. -/
theorem trial_lift_word_lower (w : List Letter) (hp : eval w=Small6.farthest)
    (hz : ∀ i,run w trialDisplacement i=0) : 18 ≤ w.length := by
  have hc := rotations_gt_of_greedy_nonzero (by decide : 2 ≤ 6) trialDisplacement
    trial_lift.1 6 1 trial_greedy_unfinished w hz
  have hpos := funext (LiftedScan.exact_positions_of_zero (by decide : 2 ≤ 6) trialDisplacement w hz)
  have hd := DirectedTokenLower.word_endpoint_lift (by decide : 2 ≤ 6) w
  rw [hp,DirectedTokenLower.cursor_eq_left_count,hpos] at hd
  simp only [add_sub_cancel_right] at hd
  have hphase : (w.count .l : Fin 6)=0 := by
    have h1 := lift_residue hd 0
    have h2 := lift_residue trial_lift 0
    have he := add_left_cancel (h1.symm.trans h2)
    simpa using he
  have hmod : w.count .l % 6=0 := by
    have hh := congrArg Fin.val hphase
    simpa using hh
  have hclower : 12 ≤ w.count .l := by omega
  have hcost := DirectedTokenLower.word_inversion_cursor_lower (by decide : 2 ≤ 6) w
  rw [hpos,DirectedTokenLower.cursor_eq_left_count] at hcost
  have hi := trial_price
  omega

#print axioms rotations_gt_of_greedy_nonzero
#print axioms trial_lift_word_lower
end LX.DirectedLowerRegression
