import LX.AffineRankOrder

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Rotation transports the cut and threshold together. The correction
at the seam is necessary because the targets are integer lifts. -/
theorem rotate_threshold_rank (hn : 2 ≤ n) (d : Fin n → ℤ) (r : Fin n) (v : ℤ) :
    thresholdRank (rotate d) r v=
      thresholdRank d (finRotate n r)
        (v+1-(if r.val=n-1 then (1 : ℤ) else 0)*n) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let turn (i : Fin n) : ℤ := if i.val=n-1 then 1 else 0
  have hval (i : Fin n) : (finRotate n i).val=if i.val=n-1 then 0 else i.val+1 := by
    rw [finRotate_apply,Fin.val_add,hv1]
    by_cases hi : i.val=n-1
    · rw [ite_eq_left hi,show i.val+1=n by omega,Nat.mod_self]
    · rw [ite_eq_right hi,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hvali (i : Fin n) : (finRotate n i : ℤ)=(i : ℤ)+1-turn i*n := by
    rw [hval]
    dsimp only [turn]
    split_ifs <;> push_cast <;> omega
  have htarget (i : Fin n) : targets (rotate d) i=targets d (finRotate n i)-1+turn i*n := by
    unfold targets rotate
    rw [hvali]
    ring
  have hleft (i : Fin n) : (targets (rotate d) i-v)/(n : ℤ)=
      (targets d (finRotate n i)-(v+1))/(n : ℤ)+turn i := by
    rw [htarget]
    have he : targets d (finRotate n i)-1+turn i*n-v=
        (targets d (finRotate n i)-(v+1))+turn i*n := by ring
    rw [he,Int.add_mul_ediv_right _ _ hnz]
  have hright (i : Fin n) :
      (targets d (finRotate n i)-(v+1-turn r*n))/(n : ℤ)=
        (targets d (finRotate n i)-(v+1))/(n : ℤ)+turn r := by
    have he : targets d (finRotate n i)-(v+1-turn r*n)=
        (targets d (finRotate n i)-(v+1))+turn r*n := by ring
    rw [he,Int.add_mul_ediv_right _ _ hnz]
  have hcut (i : Fin n) :
      turn i+(if i ≤ r then (1 : ℤ) else 0)=
        turn r+(if finRotate n i ≤ finRotate n r then (1 : ℤ) else 0) := by
    dsimp only [turn]
    simp only [Fin.le_def,hval]
    split_ifs <;> have := i.isLt <;> have := r.isLt <;> omega
  change thresholdRank (rotate d) r v=thresholdRank d (finRotate n r) (v+1-turn r*n)
  unfold thresholdRank
  rw [← Equiv.sum_comp (finRotate n) (fun i =>
    max ((targets d i-(v+1-turn r*n))/(n : ℤ)+(if i ≤ finRotate n r then 1 else 0)) 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hleft,hright]
  congr 1
  have := hcut i
  omega

theorem rotate_rank_mono (hn : 2 ≤ n) {d e : Fin n → ℤ} (hle : RankLE d e) :
    RankLE (rotate d) (rotate e) := by
  intro r v
  rw [rotate_threshold_rank hn,rotate_threshold_rank hn]
  exact hle _ _

#print axioms rotate_threshold_rank
#print axioms rotate_rank_mono
end LX.AffineScan
