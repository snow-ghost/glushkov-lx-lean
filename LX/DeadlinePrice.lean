import LX.AnchoredPhases
import LX.DepthQueue
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The number of queue steps needed once the carrier has depth zero. -/
def queueDeadline (d : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i : Fin n =>
    if backwardDepth d i=0 then 0 else (n-1)*(backwardDepth d i-1)+i.val

/-- A cursor at which the last needed exchange has already been performed. -/
def scanDeadline (d : Fin n → ℤ) : ℕ :=
  (n-1)+queueDeadline (sweep d (n-1))-1

theorem sweep_queue_deadline (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    ∀ i, backwardDepth (sweep d (queueDeadline d)) i=0 := by
  apply sweep_depth_deadline hn d hi hz
  intro j hj hjn hpos
  have hh := Finset.le_sup (f := fun i : Fin n =>
    if backwardDepth d i=0 then 0 else (n-1)*(backwardDepth d i-1)+i.val)
    (Finset.mem_univ (j : Fin n))
  change 0 < backwardDepth d (j : Fin n) at hpos
  simpa only [queueDeadline,ite_eq_right (by omega : backwardDepth d (j : Fin n) ≠ 0),
    Fin.val_natCast, Nat.mod_eq_of_lt hjn, atDepth] using hh

theorem compare_zero_of_sweep_succ_zero (d : Fin n → ℤ) (k : ℕ)
    (hz : ∀ i, sweep d (k+1) i=0) :
    ∀ i, compareHead (sweep d k) i=0 := by
  intro i
  have hh := hz ((finRotate n).symm i)
  simpa only [sweep,sweepStep,rotate,Equiv.apply_symm_apply] using hh

/-- A scalar computed from the first lap certifies the complete stopping trace. -/
theorem compare_zero_at_scan_deadline (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d)) :
    ∀ i, compareHead (sweep d (scanDeadline d)) i=0 := by
  have hei := sweep_injective hn d hi (n-1)
  have hdepth := sweep_queue_deadline hn (sweep d (n-1)) hei (sweep_head_zero hn d hi)
  have hz := zero_of_depth_zero _
    (show ∑ i, sweep (sweep d (n-1)) (queueDeadline (sweep d (n-1))) i=0 by
      rw [sweep_balance,sweep_balance,hb])
    (sweep_injective hn _ hei _) hdepth
  have he : scanDeadline d+1=(n-1)+queueDeadline (sweep d (n-1)) := by
    unfold scanDeadline
    omega
  apply compare_zero_of_sweep_succ_zero
  rw [he,sweep_add]
  exact hz

theorem ScanTrace.rotations_le_deadline (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (hb : ∑ i,d i=0)
    (hi : Function.Injective (labels d)) : w.count .l ≤ scanDeadline d :=
  ht.rotations_le_of_compare_zero hn _ (compare_zero_at_scan_deadline hn d hb hi)

/-- If a cursor bound T is certified, padding to that cursor gives an exact
word price. This keeps the final phase residue instead of charging a full lap. -/
theorem ScanTrace.word_at_cursor_zero (hn : 2 ≤ n) (p : State n) (c : Fin n)
    {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (hl : ∀ i, labels d i=p i+c) (T : ℕ) (hT : w.count .l ≤ T) :
    ∃ v : List Letter, p*eval v=1 ∧ (∀ i, run v d i=0) ∧
      v.length=inversions d+T+(c-(T : Fin n)).val := by
  let u := w ++ List.replicate (T-w.count .l) .l
  have hu : u.count .l=T := by simp only [u,List.count_append,List.count_replicate,beq_self_eq_true,ite_true]; omega
  have hz : ∀ i, run u d i=0 := by
    intro i
    dsimp only [u]
    rw [run_append,run_left_apply]
    exact ht.run_zero _
  have hv := sorting_word_of_zero hn p c d hl u hz
  refine ⟨paidWord c u,hv,?_,?_⟩
  · intro i
    simp only [paidWord,run_append,run_left_apply]
    exact hz _
  ·
    have hlen : u.length=T+inversions d := by
      simp only [u,List.length_append,List.length_replicate,length_eq_counts,
        ht.exchange_count hn hb hi]
      omega
    simp only [paidWord,List.length_append,List.length_replicate,hlen,hu]
    omega

theorem ScanTrace.word_at_cursor (hn : 2 ≤ n) (p : State n) (c : Fin n)
    {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (hl : ∀ i, labels d i=p i+c) (T : ℕ) (hT : w.count .l ≤ T) :
    ∃ v : List Letter, p*eval v=1 ∧
      v.length=inversions d+T+(c-(T : Fin n)).val := by
  obtain ⟨v,hv,_,hlen⟩ := ht.word_at_cursor_zero hn p c hb hi hl T hT
  exact ⟨v,hv,hlen⟩

#print axioms compare_zero_at_scan_deadline
#print axioms ScanTrace.word_at_cursor_zero
#print axioms ScanTrace.word_at_cursor
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

def deadlinePrice (p : State n) (a : Fin n) : ℕ :=
  inversions (displacement p a)+scanDeadline (displacement p a)+
    ((phase p a : Fin n)-(scanDeadline (displacement p a) : Fin n)).val


end LX.AnchoredPhases
