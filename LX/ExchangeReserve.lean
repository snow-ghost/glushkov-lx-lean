import LX.CrowdedDeadline
import LX.HeadReserve
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The first nonmaximal head is reached within the number of maximal-depth
positions, rather than the number of all nondescending positions. -/
theorem exists_head_with_count (d : Fin n → ℤ) (h : ℕ) (hh : 0 < h) :
    ∃ r : Fin n,r.val ≤ depthCount d h ∧ backwardDepth d r < h := by
  let P := Finset.univ.filter (fun i : Fin n => backwardDepth d i < h)
  have hP : P.Nonempty := by
    obtain ⟨i,hi⟩ := exists_zero_depth d
    exact ⟨i,by simp [P,hi,hh]⟩
  let r := P.min' hP
  have hr : backwardDepth d r < h := (Finset.mem_filter.mp (Finset.min'_mem P hP)).2
  refine ⟨r,?_,hr⟩
  apply prefix_depth_count d r.val h (Nat.le_of_lt r.isLt)
  intro j hj
  have hjn : j < n := hj.trans r.isLt
  have hval : (j : Fin n).val=j := by simp [Nat.mod_eq_of_lt hjn]
  by_contra hnot
  have hp : (j : Fin n) ∈ P := by
    simp only [P,Finset.mem_filter,Finset.mem_univ,true_and]
    change atDepth d j < h
    omega
  have hle := Finset.min'_le P (j : Fin n) hp
  change r.val ≤ (j : Fin n).val at hle
  rw [hval] at hle
  omega

/-- Charge the chosen prefix explicitly while retaining the actual number
of exchanges. This is the input needed to spend an inversion reserve. -/
theorem word_with_nonmaximal_head (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ) (r : Fin n)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d r < h) :
    ∃ v : List Letter,p*eval v=1 ∧
      (v.length : ℤ) ≤ inversions d+((h : ℤ)+1)*((n : ℤ)-1)+r.val-1 := by
  let u : List Letter := List.replicate r.val .l
  let e := run u d
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have he : e=LX.Core.RotationWords.localDisplacement d r := by
    funext i
    exact run_left_apply r.val d i
  have hei : Function.Injective (labels e) := run_injective hn u d hi
  have heb : ∑ i,e i=0 := (run_sum u d).trans hd.1
  have hem (i : Fin n) : backwardDepth e i ≤ h := by
    rw [he,recentered_backward_depth]
    exact hmax _
  have heh : backwardDepth e 0 < h := by
    rw [he,recentered_backward_depth]
    simpa only [LX.Core.AffineLift.rotation_power_apply,Fin.val_zero,Nat.cast_zero,
      Fin.cast_val_eq_self,zero_add] using hhead
  obtain ⟨w,hw⟩ := exists_scan_trace hn e heb hei
  have hL := (hw.rotations_le_deadline hn heb hei).trans
    (scan_deadline_head_reserve hn e hei h hem heh)
  have hX := hw.exchange_count hn heb hei
  have hIe : inversions e=inversions d := left_run_inversions hn d hd.1 hi r.val
  rw [hIe] at hX
  let v := paidWord (c : Fin n) (u++w)
  have hv : p*eval v=1 := by
    apply sorting_word_of_zero hn p (c : Fin n) d hl
    intro i
    rw [run_append]
    exact hw.run_zero i
  refine ⟨v,hv,?_⟩
  have hlen : v.length=r.val+w.count .l+w.count .x+
      ((c : Fin n)-((u++w).count .l : Fin n)).val := by
    simp only [v,paidWord,List.length_append,List.length_replicate,u,length_eq_counts]
    omega
  have hp := ((c : Fin n)-((u++w).count .l : Fin n)).isLt
  have hprod : 1 ≤ h*(n-1) := by
    have hh : 1 ≤ h := by omega
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hLc : (w.count .l : ℤ) ≤ (h : ℤ)*((n : ℤ)-1)-1 := by
    have hnat : w.count .l+1 ≤ h*(n-1) := by omega
    have hnat' : (w.count .l : ℤ)+1 ≤ (h : ℤ)*((n-1 : ℕ) : ℤ) := by exact_mod_cast hnat
    have hn' : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
    rw [hn'] at hnat'
    omega
  rw [hlen,hX]
  push_cast
  nlinarith

/-- Majorization pays the initial prefix using only the highest depth count.
The exchange count is left exact for subsequent arithmetic payment. -/
theorem majorized_exchange_reserve_word (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (hm : Majorized d)
    (h : ℕ) (hh : 0 < h) (hhalf : 2*h ≤ n)
    (hmax : ∀ i,backwardDepth d i ≤ h) :
    ∃ w : List Letter,p*eval w=1 ∧
      (w.length : ℤ) ≤ inversions d+(h : ℤ)*((n : ℤ)-3)+2*n-2 := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count d h hh
  have hc := top_depth_count hd hm h hhalf hmax
  obtain ⟨w,hw,hlen⟩ := word_with_nonmaximal_head hn p c d hd h r hmax hhead
  refine ⟨w,hw,?_⟩
  have hrc : (r.val : ℤ) ≤ (n : ℤ)-2*h := by omega
  nlinarith

#print axioms exists_head_with_count
#print axioms majorized_exchange_reserve_word
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

namespace LX


end LX
