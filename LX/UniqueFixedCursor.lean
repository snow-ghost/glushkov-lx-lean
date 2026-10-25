import LX.HeadReserve
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Charge an initial rotation and retain the exact final orientation.
The added prefix does not have to be part of a greedy scan trace. -/
theorem prefix_head_word_at_cursor (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ) (r : Fin n)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d r < h)
    (T : ℕ) (hT : r.val+h*(n-1)-1 ≤ T) :
    ∃ v : List Letter,p*eval v=1 ∧
      v.length=inversions d+T+((c : Fin n)-(T : Fin n)).val := by
  let u : List Letter := List.replicate r.val .l
  let e := run u d
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have he : e=LRX.RotationWords.localDisplacement d r := by
    funext i
    exact run_left_apply r.val d i
  have hei : Function.Injective (labels e) := run_injective hn u d hi
  have heb : ∑ i,e i=0 := (run_sum u d).trans hd.1
  have hem (i : Fin n) : backwardDepth e i ≤ h := by
    rw [he,recentered_backward_depth]
    exact hmax _
  have heh : backwardDepth e 0 < h := by
    rw [he,recentered_backward_depth]
    simpa only [LRX.AffineLift.rotation_power_apply,Fin.val_zero,Nat.cast_zero,
      Fin.cast_val_eq_self,zero_add] using hhead
  obtain ⟨w,hw⟩ := exists_scan_trace hn e heb hei
  have hL := (hw.rotations_le_deadline hn heb hei).trans
    (scan_deadline_head_reserve hn e hei h hem heh)
  have hX := hw.exchange_count hn heb hei
  have hIe : inversions e=inversions d := left_run_inversions hn d hd.1 hi r.val
  rw [hIe] at hX
  let v := u++w
  have hprod : 1 ≤ h*(n-1) := by
    have hh : 1 ≤ h := by omega
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hvL : v.count .l ≤ T := by
    simp only [v,u,List.count_append,List.count_replicate,beq_self_eq_true,ite_true]
    omega
  have hvX : v.count .x=inversions d := by simp [v,u,hX,List.count_replicate]
  have hvzero (i : Fin n) : run v d i=0 := by
    rw [show v=u++w from rfl,run_append]
    exact hw.run_zero i
  let z := v++List.replicate (T-v.count .l) .l
  have hzL : z.count .l=T := by
    simp only [z,List.count_append,List.count_replicate,beq_self_eq_true,ite_true]
    omega
  have hzX : z.count .x=inversions d := by simp [z,hvX,List.count_replicate]
  have hzzero (i : Fin n) : run z d i=0 := by
    simp only [z,run_append,run_left_apply]
    exact hvzero _
  have hzlen : z.length=T+inversions d := by rw [length_eq_counts,hzL,hzX]
  refine ⟨paidWord (c : Fin n) z,sorting_word_of_zero hn p (c : Fin n) d hl z hzzero,?_⟩
  simp only [paidWord,List.length_append,List.length_replicate,hzlen,hzL]
  omega

end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases
