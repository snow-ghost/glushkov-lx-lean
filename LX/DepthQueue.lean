import LX.DepthDynamics
import LX.DepthReturn
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem sweep_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) :
    Function.Injective (labels (sweep d k)) := by
  rw [← run_sweep_word]
  exact run_injective hn _ d hi

theorem sweep_balance (d : Fin n → ℤ) (k : ℕ) :
    ∑ i, sweep d k i = ∑ i, d i := by
  rw [← run_sweep_word, run_sum]

theorem sweep_step_last_depth (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atDepth (sweepStep d) (n-1) =
      if d 1+1 < d 0 then backwardDepth d 1-1 else backwardDepth d 0 := by
  rw [sweepStep, at_depth_rotate hn, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  simp only [atDepth, Fin.natCast_self, compareHead]
  split_ifs with hd
  · have hh := exchange_backward_depth hn d hd
    omega
  · rfl

theorem sweep_step_tail_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ)
    (hj : 0 < j) (hjn : j+1 < n) :
    atDepth (sweepStep d) j = atDepth d (j+1) := by
  rw [sweepStep, at_depth_rotate hn, compare_head_tail_depth hn _ (j+1) (by omega) hjn]

theorem sweep_depth_le (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hd : ∀ i, backwardDepth d i ≤ h) (k : ℕ) :
    ∀ i, backwardDepth (sweep d k) i ≤ h := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    intro i
    have hinj := sweep_injective hn d hi k
    by_cases hi0 : i=0
    · subst i
      rw [sweep, sweep_step_head_depth hn _ hinj]
      exact (min_le_left _ _).trans (ih 0)
    · have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      suffices hs : atDepth (sweepStep (sweep d k)) i.val ≤ h by
        simpa [atDepth,sweep] using hs
      by_cases hil : i.val=n-1
      · rw [hil, sweep_step_last_depth hn]
        split_ifs <;> have h0 := ih 0 <;> have h1 := ih 1 <;> omega
      · rw [sweep_step_tail_depth hn _ _ hip (by have := i.isLt; omega)]
        exact ih _

theorem exists_zero_depth (d : Fin n → ℤ) : ∃ i, backwardDepth d i=0 := by
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) d
    ⟨0, Finset.mem_univ _⟩
  refine ⟨a, ?_⟩
  unfold backwardDepth
  apply Finset.sum_eq_zero
  intro j _
  have hj := ha j (Finset.mem_univ _)
  have hval := (j-a).isLt
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hq : LX.Core.AffineLift.crossingNumerator d a j / (n : ℤ) < 1 := by
    apply (Int.ediv_lt_iff_lt_mul hn).mpr
    simp only [LX.Core.AffineLift.crossingNumerator]
    omega
  simp only [LX.Core.AffineLift.crossing, neg_neg]
  omega

theorem sweep_prefix_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) (hk : k < n) :
    (∀ j ≤ k, backwardDepth (sweep d k) 0 ≤ atDepth d j) ∧
    ∀ j : ℕ, 0 < j → j+k < n → atDepth (sweep d k) j = atDepth d (j+k) := by
  induction k with
  | zero => simp [sweep, atDepth]
  | succ k ih =>
    obtain ⟨hh,ht⟩ := ih (by omega)
    constructor
    · intro j hj
      rw [sweep, sweep_step_head_depth hn _ (sweep_injective hn d hi k)]
      by_cases hjk : j ≤ k
      · exact (min_le_left _ _).trans (hh j hjk)
      · have he : j=1+k := by omega
        have he1 := ht 1 (by omega) (by omega)
        change backwardDepth (sweep d k) 1 = atDepth d (1+k) at he1
        rw [he, ← he1]
        exact min_le_right _ _
    · intro j hj hjk
      rw [sweep, sweep_step_tail_depth hn _ j hj (by omega), ht (j+1) (by omega) (by omega)]
      congr 1 <;> omega

theorem sweep_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : backwardDepth (sweep d (n-1)) 0=0 := by
  obtain ⟨i,hi0⟩ := exists_zero_depth d
  have hh := (sweep_prefix_depth hn d hi (n-1) (by omega)).1 i.val (by have := i.isLt; omega)
  simpa [atDepth, hi0] using hh

/-- After a zero-depth carrier is reached, the tail is a queue: it shifts once
and its first depth is decremented when appended at the other end. -/
theorem sweep_step_zero_queue (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    backwardDepth (sweepStep d) 0=0 ∧
      atDepth (sweepStep d) (n-1)=backwardDepth d 1-1 := by
  constructor
  · rw [sweep_step_head_depth hn d hi, hz, Nat.zero_min]
  · rw [sweep_step_last_depth hn]
    split_ifs with hdesc
    · rfl
    · have hh := sweep_step_head_depth hn d hi
      have he : sweepStep d=rotate d := by simp [sweepStep,compareHead,hdesc]
      rw [he,rotate_backward_depth hn] at hh
      simp only [finRotate_apply, zero_add, hz, Nat.zero_min] at hh
      omega

/-- Each positive queue entry has a deadline. Every step reduces all deadlines
by one, including the entry that wraps around the cursor. -/
theorem sweep_depth_deadline (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0)
    (k : ℕ) (hk : ∀ j : ℕ, 0 < j → j < n → 0 < atDepth d j →
      (n-1)*(atDepth d j-1)+j ≤ k) :
    ∀ i, backwardDepth (sweep d k) i=0 := by
  induction k generalizing d with
  | zero =>
    intro i
    by_cases hi0 : i=0
    · simpa [sweep,hi0] using hz
    · have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      have hh := hk i.val hip i.isLt
      simp only [atDepth, Fin.cast_val_eq_self] at hh
      simp only [sweep]
      by_contra hnot
      have hh' := hh (by omega)
      omega
  | succ k ih =>
    rw [sweep_succ_start]
    have hinj := sweep_injective hn d hi 1
    change Function.Injective (labels (sweepStep d)) at hinj
    have hqueue := sweep_step_zero_queue hn d hi hz
    apply ih (sweepStep d) hinj hqueue.1
    intro j hj hjn hpos
    by_cases hjl : j=n-1
    · subst j
      rw [hqueue.2] at hpos ⊢
      have hb : 1 < backwardDepth d 1 := by omega
      have hh := hk 1 (by omega) (by omega) (by exact Nat.zero_lt_of_lt hb)
      change (n-1)*(backwardDepth d 1-1)+1 ≤ k+1 at hh
      have he : (n-1)*(backwardDepth d 1-1-1)+(n-1) =
          (n-1)*(backwardDepth d 1-1) := by
        rw [← Nat.mul_add_one]
        congr 1
        omega
      rw [he]
      omega
    · rw [sweep_step_tail_depth hn _ j hj (by omega)] at hpos ⊢
      have hh := hk (j+1) (by omega) (by omega) hpos
      omega

theorem zero_of_depth_zero (d : Fin n → ℤ) (hb : ∑ i, d i=0)
    (hi : Function.Injective (labels d)) (hz : ∀ i, backwardDepth d i=0) :
    ∀ i, d i=0 := by
  let p : State n := Equiv.ofBijective (labels d) ⟨hi, Finite.surjective_of_injective hi⟩
  have hd : LX.Core.AffineLift.IsLift p.symm 0 d := by
    refine ⟨hb, ?_⟩
    intro i
    apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self, Int.cast_zero, add_zero,
      Equiv.symm_symm]
    rfl
  have hcross (i j : Fin n) : LX.Core.AffineLift.crossing d i j=0 := by
    have hlo : 0 ≤ LX.Core.AffineLift.crossing d i j := by
      have hh : (-LX.Core.AffineLift.crossing d i j).toNat ≤ backwardDepth d i :=
        Finset.single_le_sum (f := fun k => (-LX.Core.AffineLift.crossing d i k).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hz] at hh
      omega
    have hhi := maximum_depth_nonpositive_crossings d i (by intro k; simp only [hz,le_refl]) j
    omega
  intro i
  have hh := LX.Core.AffineLift.crossing_row_sum hd i
  simpa only [hcross,Finset.sum_const_zero] using hh.symm

theorem sweep_add (d : Fin n → ℤ) (a b : ℕ) :
    sweep d (a+b)=sweep (sweep d a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg sweepStep ih

/-- A depth bound h gives a concrete quadratic stopping time for the actual scan. -/
theorem sweep_zero_of_depth_bound (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i=0) (hi : Function.Injective (labels d))
    (h : ℕ) (hd : ∀ i, backwardDepth d i ≤ h) :
    ∀ i, sweep d ((n-1)+(n-1)*h) i=0 := by
  let e := sweep d (n-1)
  have hei : Function.Injective (labels e) := sweep_injective hn d hi _
  have heh : ∀ i, backwardDepth e i ≤ h := sweep_depth_le hn d hi h hd _
  have hz := sweep_depth_deadline hn e hei (sweep_head_zero hn d hi) ((n-1)*h)
  have hz' : ∀ i, backwardDepth (sweep e ((n-1)*h)) i=0 := by
    apply hz
    intro j hj hjn hpos
    have hh := heh (j : Fin n)
    change atDepth e j ≤ h at hh
    have he : atDepth e j-1+1=atDepth e j := by omega
    have hmul := Nat.mul_le_mul_left (n-1) hh
    rw [← he, Nat.mul_add, Nat.mul_one] at hmul
    omega
  rw [sweep_add]
  apply zero_of_depth_zero _ _ (sweep_injective hn e hei _) hz'
  rw [sweep_balance,sweep_balance,hb]

theorem ScanTrace.rotations_le_depth (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (hb : ∑ i, d i=0)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hd : ∀ i, backwardDepth d i ≤ h) : w.count .l ≤ (h+1)*(n-1) := by
  have hz := sweep_zero_of_depth_bound hn d hb hi h hd
  have he : (n-1)+(n-1)*h=(h+1)*(n-1) := by ring
  rw [he] at hz
  apply ht.rotations_le_of_compare_zero hn
  intro i
  simp [compareHead,hz]

#print axioms sweep_depth_deadline
#print axioms sweep_head_zero
#print axioms zero_of_depth_zero
#print axioms sweep_zero_of_depth_bound
#print axioms ScanTrace.rotations_le_depth
end LX.AffineScan
