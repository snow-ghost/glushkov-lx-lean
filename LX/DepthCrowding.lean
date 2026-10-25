import LRX.BalancedSubsetEnergy
import LX.DepthBound
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- An outgoing inversion always ends at a token of strictly larger backward depth. -/
theorem crossing_pos_depth_lt (d : Fin n → ℤ) (a j : Fin n)
    (h : 0 < LRX.AffineLift.crossing d a j) : backwardDepth d a < backwardDepth d j := by
  let r := LRX.L n ^ a.val
  let b : Fin n := r.symm j
  let e := LRX.RotationWords.localDisplacement d a
  have hr0 : r 0=a := by simp [r,LRX.AffineLift.rotation_power_apply]
  have hrb : r b=j := r.apply_symm_apply j
  have hc : LRX.AffineLift.crossing e 0 b=LRX.AffineLift.crossing d a j := by
    have hh := LRX.RotationWords.crossing_recentered d a 0 b
    change LRX.AffineLift.crossing e 0 b=LRX.AffineLift.crossing d (r 0) (r b) at hh
    simpa only [hr0,hrb] using hh
  have htarget : targets e b < targets e 0 := by
    have hh : 0 < LRX.AffineLift.crossing e 0 b := by omega
    have hnum : LRX.AffineLift.crossingNumerator e 0 b=targets e b-targets e 0 := by
      simp [LRX.AffineLift.crossingNumerator,targets]
    simp only [LRX.AffineLift.crossing,hnum] at hh
    by_contra hnot
    have hq := Int.ediv_nonneg (by omega : 0 ≤ targets e b-targets e 0)
      (show (0 : ℤ) ≤ n by positivity)
    omega
  have hlt := backward_depth_gt_head e b htarget
  have h0 := recentered_backward_depth d a 0
  have hb := recentered_backward_depth d a b
  change backwardDepth e 0=backwardDepth d (r 0) at h0
  change backwardDepth e b=backwardDepth d (r b) at hb
  rwa [h0,hb,hr0,hrb] at hlt

/-- Net displacement plus incoming crossings is exactly the outgoing crossing count. -/
theorem displacement_add_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (i : Fin n) :
    d i+(backwardDepth d i : ℤ)=
      ∑ j, ((LRX.AffineLift.crossing d i j).toNat : ℤ) := by
  rw [← LRX.AffineLift.crossing_row_sum hd i]
  simp only [backwardDepth,Nat.cast_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  omega

def depthCount (d : Fin n → ℤ) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => k ≤ backwardDepth d i).card

/-- A token can only send unit crossings to tokens above it in the depth ordering. -/
theorem displacement_add_depth_le_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (hm : LRX.AffineLift.Majorized d)
    (k : ℕ) (i : Fin n) (hk : k ≤ backwardDepth d i) :
    d i+(backwardDepth d i : ℤ) ≤ depthCount d (k+1) := by
  rw [displacement_add_depth hd]
  have hterm (j : Fin n) : ((LRX.AffineLift.crossing d i j).toNat : ℤ) ≤
      if k+1 ≤ backwardDepth d j then 1 else 0 := by
    have hc := LRX.AffineLift.crossing_unit hd.1 hm i j
    by_cases hpos : 0 < LRX.AffineLift.crossing d i j
    · have hh := crossing_pos_depth_lt d i j hpos
      rw [ite_eq_left (by omega : k+1 ≤ backwardDepth d j)]
      have hh' := le_abs_self (LRX.AffineLift.crossing d i j)
      omega
    · have he : (LRX.AffineLift.crossing d i j).toNat=0 := by omega
      rw [he,Nat.cast_zero]
      split_ifs <;> norm_num
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j)
  simpa [depthCount] using hh

/-- Majorization bounds the number of coordinates below any fixed threshold. -/
theorem majorized_lower_threshold {d : Fin n → ℤ}
    (hb : ∑ i,d i=0) (hm : LRX.AffineLift.Majorized d)
    (S : Finset (Fin n)) (t : ℤ) (ht : 2*t ≤ (n : ℤ))
    (hS : ∀ i ∈ S, d i ≤ -t) : (S.card : ℤ) ≤ (n : ℤ)-2*t := by
  have hmaj := LRX.AffineLift.majorized_neg hb hm S
  have hs : (S.card : ℤ)*t ≤ ∑ i ∈ S, -d i := by
    calc
      _ = ∑ _i ∈ S, t := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by have := hS i hi; omega)
  by_cases he : S.card=0
  · simp only [he,Nat.cast_zero]
    omega
  · have hp : (0 : ℤ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero he
    nlinarith

/-- Only a bounded number of tokens can have near-maximal depth. The bound
uses the next level, so it can be iterated down from the largest depth. -/
theorem depth_count_recurrence {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (hm : LRX.AffineLift.Majorized d)
    (k : ℕ) (hk : 2*k ≤ n) :
    (depthCount d k : ℤ) ≤ (n : ℤ)-2*k+2*depthCount d (k+1) := by
  have hh : (depthCount d k : ℤ) ≤ (n : ℤ)-2*((k : ℤ)-depthCount d (k+1)) := by
    apply majorized_lower_threshold hd.1 hm _ ((k : ℤ)-depthCount d (k+1))
    · omega
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hb := displacement_add_depth_le_count hd hm k i hi'
      omega
  linarith

theorem top_depth_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (hm : LRX.AffineLift.Majorized d)
    (h : ℕ) (hh : 2*h ≤ n) (hmax : ∀ i, backwardDepth d i ≤ h) :
    (depthCount d h : ℤ) ≤ (n : ℤ)-2*h := by
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have := hmax i
    omega
  have hc := depth_count_recurrence hd hm h hh
  simpa only [hz,Nat.cast_zero,mul_zero,add_zero] using hc


#print axioms crossing_pos_depth_lt
#print axioms depth_count_recurrence
end LX.AffineScan
