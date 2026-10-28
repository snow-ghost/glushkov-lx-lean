import LX.DeadlinePrice
import LX.FirstLapFormula
import LX.GreedyRotationOptimality
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

private theorem queue_term_le (d : Fin n → ℤ) (j : ℕ) (hj : j < n) :
    (if atDepth d j=0 then 0 else (n-1)*(atDepth d j-1)+j) ≤ queueDeadline d := by
  have hh := Finset.le_sup (f := fun i : Fin n =>
    if backwardDepth d i=0 then 0 else (n-1)*(backwardDepth d i-1)+i.val)
    (Finset.mem_univ (j : Fin n))
  convert hh using 1 <;>
    simp only [queueDeadline,atDepth,Fin.val_natCast,Nat.mod_eq_of_lt hj] <;> rfl

/-- A queue step cannot remove more than one unit of remaining deadline.
This is the lower counterpart of the existing completion bound. -/
theorem queue_deadline_step_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    queueDeadline d ≤ queueDeadline (sweepStep d)+1 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  apply Finset.sup_le
  intro i _
  by_cases hi0 : i=0
  · subst i; simp [hz]
  · by_cases hb0 : backwardDepth d i=0
    · simp [hb0]
    · simp only [ite_eq_right hb0]
      have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      by_cases hi1 : i=1
      · subst i
        rw [hv1]
        have hq := sweep_step_zero_queue hn d hi hz
        have ht := queue_term_le (sweepStep d) (n-1) (by omega)
        rw [hq.2] at ht
        by_cases hb1 : backwardDepth d 1=1
        · simp [hb1]
        · have hb2 : 2 ≤ backwardDepth d 1 := by omega
          rw [ite_eq_right (by omega : backwardDepth d 1-1 ≠ 0)] at ht
          have he : (n-1)*(backwardDepth d 1-1-1)+(n-1)=
              (n-1)*(backwardDepth d 1-1) := by
            rw [← Nat.mul_add_one]
            congr 1
            omega
          rw [he] at ht
          omega
      · have hip2 : 2 ≤ i.val := by
          have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (by omega))
          omega
        have ht := queue_term_le (sweepStep d) (i.val-1) (by have := i.isLt; omega)
        rw [sweep_step_tail_depth hn d (i.val-1) (by omega) (by have := i.isLt; omega),
          Nat.sub_add_cancel (by omega : 1 ≤ i.val)] at ht
        simp only [atDepth,Fin.cast_val_eq_self] at ht
        rw [ite_eq_right hb0] at ht
        omega

theorem queue_deadline_sweep_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) (k : ℕ) :
    queueDeadline d ≤ queueDeadline (sweep d k)+k := by
  induction k generalizing d with
  | zero => simp [sweep]
  | succ k ih =>
    have hs := queue_deadline_step_lower hn d hi hz
    have hnext := (sweep_step_zero_queue hn d hi hz).1
    have hinj : Function.Injective (labels (sweepStep d)) := sweep_injective hn d hi 1
    have ht := ih (sweepStep d) hinj hnext
    rw [sweep_succ_start]
    omega

theorem queue_deadline_of_zero (d : Fin n → ℤ) (hz : ∀ i,d i=0) : queueDeadline d=0 := by
  have he : d=(fun _ => 0) := funext hz
  subst d
  have hd : LX.Core.AffineLift.IsLift (1 : State n) 0 (fun _ => 0) := by
    simpa only [← Equiv.Perm.inv_def,inv_one,Equiv.Perm.one_apply,sub_self] using
      LX.Core.AffineLift.canonical_lift (1 : State n)
  have hb (i : Fin n) : backwardDepth (fun _ : Fin n => 0) i=0 := by
    have hh := backward_depth_le_strip hd (0 : ℤ) (by simp) i
    omega
  simp [queueDeadline,hb]

theorem sweep_zero_persists (d : Fin n → ℤ) {a b : ℕ} (hab : a ≤ b)
    (hz : ∀ i,sweep d a i=0) : ∀ i,sweep d b i=0 := by
  have hzero (k : ℕ) : sweep (fun _ : Fin n => 0) k=(fun _ => 0) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [sweep,ih]; funext i; simp [sweepStep,compareHead,rotate]
  rw [show b=a+(b-a) by omega,sweep_add,funext hz,hzero]
  simp

/-- If the first lap leaves a positive queue, its deadline is also a
lower bound for every word realizing the same exact lift. -/
theorem scan_deadline_le_any_word (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (hq : 0 < queueDeadline (sweep d (n-1))) (w : List Letter)
    (hw : ∀ i,run w d i=0) : scanDeadline d ≤ w.count .l := by
  have hz := saturated_sweep_zero_of_word hn d w hb hw
  have hs : ∀ i,sweep d (w.count .l+1) i=0 := by
    intro i
    change saturatedSweep d (w.count .l) (finRotate n i)=0
    exact hz _
  have hstart : n-1 ≤ w.count .l+1 := by
    by_contra hnot
    have he := sweep_zero_persists d (by omega : w.count .l+1 ≤ n-1) hs
    have hq0 := queue_deadline_of_zero _ he
    omega
  have hqueue := queue_deadline_sweep_lower hn (sweep d (n-1))
    (sweep_injective hn d hi _) (sweep_head_zero hn d hi) (w.count .l+1-(n-1))
  have he : ∀ i,sweep (sweep d (n-1)) (w.count .l+1-(n-1)) i=0 := by
    rw [← sweep_add,show n-1+(w.count .l+1-(n-1))=w.count .l+1 by omega]
    exact hs
  rw [queue_deadline_of_zero _ he,zero_add] at hqueue
  unfold scanDeadline
  omega


/-- A positive depth emitted at position j forces this many rotations,
even if the word uses a different sequence of exchanges. -/
theorem emitted_depth_rotation_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (j H : ℕ) (hj : 0 < j) (hjn : j < n) (hH : 0 < H)
    (he : H ≤ emittedDepth d j) (w : List Letter) (hw : ∀ i,run w d i=0) :
    (n-1)*H+j-1 ≤ w.count .l := by
  have hjv : (j : Fin n).val=j := Nat.mod_eq_of_lt hjn
  have hj0 : (j : Fin n) ≠ 0 := by
    intro hh
    have := congrArg Fin.val hh
    simp only [hjv,Fin.val_zero] at this
    omega
  have hdepth := first_lap_depth_formula hn d hi (j : Fin n)
  rw [ite_eq_right hj0,hjv] at hdepth
  have hterm := queue_term_le (sweep d (n-1)) j hjn
  change (if backwardDepth (sweep d (n-1)) (j : Fin n)=0 then 0
    else (n-1)*(backwardDepth (sweep d (n-1)) (j : Fin n)-1)+j) ≤ _ at hterm
  rw [hdepth,ite_eq_right (by omega : emittedDepth d j ≠ 0)] at hterm
  have hq : 0 < queueDeadline (sweep d (n-1)) := by omega
  have ht := scan_deadline_le_any_word hn d hb hi hq w hw
  have hm := Nat.mul_le_mul_left (n-1) (show H-1 ≤ emittedDepth d j-1 by omega)
  have ha : (n-1)*(H-1)+(n-1)=(n-1)*H := by
    rw [← Nat.mul_add_one,Nat.sub_add_cancel hH]
  unfold scanDeadline at ht
  omega

/-- When j is a new prefix record, the minimum predecessor depth in that
prefix survives into the queue. -/
theorem prefix_record_rotation_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (j H : ℕ) (hj : 0 < j) (hjn : j < n) (hH : 0 < H)
    (hr : ∀ i : Fin j, atTarget d i.val ≤ atTarget d j)
    (hd : ∀ k < j,H ≤ atDepth d k)
    (w : List Letter) (hw : ∀ i,run w d i=0) :
    (n-1)*H+j-1 ≤ w.count .l := by
  apply emitted_depth_rotation_lower hn d hb hi j H hj hjn hH _ w hw
  have hnot : ¬ ∃ i : Fin j,atTarget d j < atTarget d i.val := by
    rintro ⟨i,h⟩
    have := hr i
    omega
  rw [emittedDepth,ite_eq_right hnot]
  exact (prefix_minimum_le_iff _ _ _).mpr (fun k hk => hd k (by omega))

#print axioms scan_deadline_le_any_word
#print axioms prefix_record_rotation_lower
end LX.AffineScan
