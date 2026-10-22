import LX.GreedyRotationOptimality
import LX.DirectedLiftLower
import LX.LiftedScanBridge

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The exact physical endpoint of an arbitrary word is a board on which
that same word terminates at zero. Winding is retained. -/
theorem exists_exact_word_board (hn : 2 ≤ n) (w : List Letter) :
    ∃ d : Fin n → ℤ,IsLift (eval w) (w.count .l : ℤ) d ∧ ∀ i,run w d i=0 := by
  let s := LRX.LiftedModel.run (w.map Letter.toLRX) (LRX.LiftedModel.initial (n := n))
  let d : Fin n → ℤ := fun i => s.position i-(i : ℤ)
  have hd : IsLift (eval w) (w.count .l : ℤ) d := by
    have hh := DirectedTokenLower.word_endpoint_lift hn w
    rw [DirectedTokenLower.cursor_eq_left_count] at hh
    exact hh
  refine ⟨d,hd,?_⟩
  have he : targets d=s.position := by funext i; simp [targets,d]
  have hr := LiftedScan.remainder_run hn (targets d) w LRX.LiftedModel.initial
  rw [LiftedScan.remainder_initial] at hr
  intro i
  rw [← hr]
  change targets d (LiftedScan.visible s i)-s.position (LiftedScan.visible s i)=0
  rw [he,sub_self]

/-- Greedy scheduling plus the exact final rotation is no longer than
any word reaching the same lifted endpoint and cursor residue. -/
theorem ScanTrace.paid_length_le_any_word (hn : 2 ≤ n) {d : Fin n → ℤ}
    {g : List Letter} (hg : ScanTrace d g) (hb : ∑ i,d i=0)
    (hi : Function.Injective (labels d)) (w : List Letter) (hw : ∀ i,run w d i=0) :
    (paidWord (w.count .l : Fin n) g).length ≤ w.length := by
  have hrot := hg.rotations_le_any_word hn hb w hw
  have hcost := DirectedTokenLower.word_inversion_cursor_lower hn w
  have hpos := funext (LiftedScan.exact_positions_of_zero hn d w hw)
  rw [hpos,DirectedTokenLower.cursor_eq_left_count] at hcost
  change (inversions d : ℤ)+(w.count .l : ℤ) ≤ (w.length : ℤ) at hcost
  have hcost' : inversions d+w.count .l ≤ w.length := by exact_mod_cast hcost
  have hpad : ((w.count .l : Fin n)-(g.count .l : Fin n)).val ≤ w.count .l-g.count .l := by
    rw [← Nat.cast_sub hrot,Fin.val_natCast]
    exact Nat.mod_le _ _
  rw [hg.paid_length hn hb hi]
  unfold paidRotations
  omega

/-- A genuine normal form for every LX word: a greedy scan of some
balanced exact lift, followed by its paid final rotation, never costs more. -/
theorem exists_greedy_normal_form (hn : 2 ≤ n) (w : List Letter) :
    ∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift (eval w) (w.count .l : ℤ) d ∧ ScanTrace d g ∧
      eval (n := n) (paidWord (w.count .l : Fin n) g)=eval w ∧
      (paidWord (w.count .l : Fin n) g).length ≤ w.length := by
  obtain ⟨d,hd,hzero⟩ := exists_exact_word_board hn w
  obtain ⟨g,hg,hgword⟩ := exists_realized_scan hn (eval w).symm (w.count .l : ℤ) d
    (by simpa only [Equiv.symm_symm] using hd)
  have hlabels (i : Fin n) : labels d i=(eval w).symm i+(w.count .l : Fin n) := by
    simpa only [labels,Int.cast_natCast] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hlabels,hlabels] at hij
    exact (eval w).symm.injective (add_right_cancel hij)
  refine ⟨d,g,hd,hg,?_,hg.paid_length_le_any_word hn hd.1 hi w hzero⟩
  have he : (eval (n := n) w)⁻¹*eval (paidWord (w.count .l : Fin n) g)=1 := by
    simpa only [paidWord,Int.cast_natCast,Equiv.Perm.inv_def] using hgword
  exact (inv_mul_eq_one.mp he).symm

end LX.AffineScan

namespace LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every directed distance is attained within the proved greedy normal
form family. No restriction to minimum energy or minimum height is made. -/
theorem exists_shortest_greedy_word (hn : 2 ≤ n) (p : State n) :
    ∃ c : ℕ,∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift p (c : ℤ) d ∧ ScanTrace d g ∧
      eval (paidWord (c : Fin n) g)=p ∧
      (paidWord (c : Fin n) g).length=length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  obtain ⟨d,g,hd,hg,he,hbound⟩ := exists_greedy_normal_form hn w
  rw [hw] at hd he
  refine ⟨w.count .l,?_⟩
  refine ⟨d,?_⟩
  refine ⟨g,?_⟩
  refine ⟨hd,?_⟩
  refine ⟨hg,?_⟩
  refine ⟨he,?_⟩
  have hlo := length_le_word (n := n) (paidWord (w.count .l : Fin n) g)
  rw [he] at hlo
  exact Nat.le_antisymm (hbound.trans_eq hlen) hlo

#print axioms AffineScan.exists_greedy_normal_form
#print axioms exists_shortest_greedy_word
end LX
