import LX.ScanInversions
import LX.SweepCarrier

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Counts periodic copies of targets at least v to the left of cut r.
The infinite periodic board is represented by a finite sum of quotients. -/
def thresholdRank (d : Fin n → ℤ) (r : Fin n) (v : ℤ) : ℤ :=
  ∑ i : Fin n,max ((targets d i-v)/(n : ℤ)+(if i ≤ r then 1 else 0)) 0

def RankLE (d e : Fin n → ℤ) : Prop :=
  ∀ r v,thresholdRank d r v ≤ thresholdRank e r v

omit [NeZero n] in
theorem rank_le_refl (d : Fin n → ℤ) : RankLE d d := fun _ _ => le_rfl

omit [NeZero n] in
theorem rank_le_trans {d e f : Fin n → ℤ} (hde : RankLE d e) (hef : RankLE e f) :
    RankLE d f := fun r v => (hde r v).trans (hef r v)

private theorem split_head_sum (hn : 2 ≤ n) (f : Fin n → ℤ) :
    (∑ i : Fin n,f i)=(∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,f i)+f 0+f 1 := by
  have h10 : (1 : Fin n) ≠ 0 := by intro h; have := Fin.one_eq_zero_iff.mp h; omega
  have h0 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) f (Finset.mem_univ 0)
  have h1 := Finset.sum_erase_add (s := Finset.univ.erase (0 : Fin n)) f
    (Finset.mem_erase.mpr ⟨h10,Finset.mem_univ 1⟩)
  omega

private def rankTail (d : Fin n → ℤ) (v : ℤ) : ℤ :=
  ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,max ((targets d i-v)/(n : ℤ)) 0

theorem threshold_rank_head (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d 0 v=rankTail d v+
      max ((targets d 0-v)/(n : ℤ)+1) 0+max ((targets d 1-v)/(n : ℤ)) 0 := by
  have h10 : (1 : Fin n) ≠ 0 := by intro h; have := Fin.one_eq_zero_iff.mp h; omega
  rw [thresholdRank,split_head_sum hn]
  have ht : (∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,
      max ((targets d i-v)/(n : ℤ)+(if i ≤ 0 then 1 else 0)) 0)=rankTail d v := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hnot : ¬i ≤ 0 := by simpa using hi0
    simp [hnot]
  rw [ht]
  simp [show ¬(1 : Fin n) ≤ 0 by simpa using h10]

theorem threshold_rank_one (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d 1 v=rankTail d v+
      max ((targets d 0-v)/(n : ℤ)+1) 0+max ((targets d 1-v)/(n : ℤ)+1) 0 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  rw [thresholdRank,split_head_sum hn]
  have ht : (∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,
      max ((targets d i-v)/(n : ℤ)+(if i ≤ 1 then 1 else 0)) 0)=rankTail d v := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 := (Finset.mem_erase.mp hi).1
    have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hnot : ¬i ≤ 1 := by
      change ¬i.val ≤ (1 : Fin n).val
      have hne0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (by omega))
      omega
    simp [hnot]
  rw [ht]
  simp

theorem threshold_rank_before_head (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d ⟨n-1,by omega⟩ (v+n)=rankTail d v+
      max ((targets d 0-v)/(n : ℤ)) 0+max ((targets d 1-v)/(n : ℤ)) 0 := by
  have he (i : Fin n) :
      (targets d i-(v+n))/(n : ℤ)+1=(targets d i-v)/(n : ℤ) := by
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have ha : targets d i-(v+n)=(targets d i-v)+(-1)*(n : ℤ) := by ring
    rw [ha,Int.add_mul_ediv_right _ _ hnz]
    omega
  unfold thresholdRank
  have hle (i : Fin n) : i ≤ (⟨n-1,by omega⟩ : Fin n) := by change i.val ≤ n-1; omega
  simp_rw [ite_eq_left (hle _),he]
  exact split_head_sum hn _

private theorem compare_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    rankTail (compareHead d) v=rankTail d v := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 := (Finset.mem_erase.mp hi).1
  have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have ht : targets (compareHead d) i=targets d i := by
    unfold compareHead
    split_ifs
    · rw [exchange_targets hn,Equiv.swap_apply_of_ne_of_ne hi0 hi1]
    · rfl
  rw [ht]

private theorem compare_rank_levels (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    (targets (compareHead d) 0-v)/(n : ℤ)=
        min ((targets d 0-v)/(n : ℤ)) ((targets d 1-v)/(n : ℤ)) ∧
    (targets (compareHead d) 1-v)/(n : ℤ)=
        max ((targets d 0-v)/(n : ℤ)) ((targets d 1-v)/(n : ℤ)) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h0 : targets (compareHead d) 0=min (targets d 0) (targets d 1) := by
    simpa only [targets,atTarget,Fin.val_zero,Nat.cast_zero,hv1,Nat.cast_one,zero_add] using compare_head_zero hn d
  have h1 : targets (compareHead d) 1=max (targets d 0) (targets d 1) := by
    simpa only [targets,atTarget,Fin.val_zero,Nat.cast_zero,hv1,Nat.cast_one,zero_add] using compare_head_one hn d
  rw [h0,h1]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  rcases le_total (targets d 0) (targets d 1) with h | h
  · have hq := Int.ediv_le_ediv hnpos (show targets d 0-v ≤ targets d 1-v by omega)
    rw [min_eq_left h,max_eq_right h,min_eq_left hq,max_eq_right hq]
    exact ⟨rfl,rfl⟩
  · have hq := Int.ediv_le_ediv hnpos (show targets d 1-v ≤ targets d 0-v by omega)
    rw [min_eq_right h,max_eq_left h,min_eq_right hq,max_eq_left hq]
    exact ⟨rfl,rfl⟩

/-- Exact local rank update for the actual LX comparator. The cut just
before the head uses the preceding periodic copy, hence threshold v+n. -/
theorem compare_threshold_rank_head (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank (compareHead d) 0 v=
      max (thresholdRank d ⟨n-1,by omega⟩ (v+n)) (thresholdRank d 1 v-1) := by
  rw [threshold_rank_head hn,compare_rank_tail hn,
    (compare_rank_levels hn d v).1,(compare_rank_levels hn d v).2,
    threshold_rank_before_head hn,threshold_rank_one hn]
  omega

theorem exchange_threshold_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ)
    (r : Fin n) (hr : r ≠ 0) (v : ℤ) :
    thresholdRank (exchange d) r v=thresholdRank d r v := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h1r : (1 : Fin n) ≤ r := by
    have hne : r.val ≠ 0 := fun h => hr (Fin.ext h)
    change (1 : Fin n).val ≤ r.val
    omega
  have hp (i : Fin n) : Equiv.swap 0 1 i ≤ r ↔ i ≤ r := by
    by_cases hi0 : i=0
    · subst i; simp [h1r]
    · by_cases hi1 : i=1
      · subst i; simp [h1r]
      · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  unfold thresholdRank
  simp_rw [exchange_targets hn]
  calc
    _ = ∑ i : Fin n,max ((targets d (Equiv.swap 0 1 i)-v)/(n : ℤ)+
        (if Equiv.swap 0 1 i ≤ r then 1 else 0)) 0 := by simp_rw [hp]
    _ = _ := Equiv.sum_comp (Equiv.swap (0 : Fin n) 1)
      (fun i : Fin n => max ((targets d i-v)/(n : ℤ)+(if i ≤ r then 1 else 0)) 0)

theorem compare_threshold_rank_tail (hn : 2 ≤ n) (d : Fin n → ℤ)
    (r : Fin n) (hr : r ≠ 0) (v : ℤ) :
    thresholdRank (compareHead d) r v=thresholdRank d r v := by
  unfold compareHead
  split_ifs
  · exact exchange_threshold_rank_tail hn d r hr v
  · rfl

theorem compare_rank_le_self (hn : 2 ≤ n) (d : Fin n → ℤ) : RankLE (compareHead d) d := by
  intro r v
  by_cases hr : r=0
  · subst r
    rw [compare_threshold_rank_head hn,threshold_rank_before_head hn,
      threshold_rank_one hn,threshold_rank_head hn]
    omega
  · rw [compare_threshold_rank_tail hn d r hr]

theorem compare_rank_mono (hn : 2 ≤ n) {d e : Fin n → ℤ} (hle : RankLE d e) :
    RankLE (compareHead d) (compareHead e) := by
  intro r v
  by_cases hr : r=0
  · subst r
    rw [compare_threshold_rank_head hn,compare_threshold_rank_head hn]
    exact max_le_max (hle _ _) (by have := hle 1 v; omega)
  · rw [compare_threshold_rank_tail hn d r hr,compare_threshold_rank_tail hn e r hr]
    exact hle r v

theorem compare_exchange_eq (hn : 2 ≤ n) (d : Fin n → ℤ) :
    compareHead (exchange d)=compareHead d := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have he : exchange (exchange d)=d := by
    funext i
    by_cases hi0 : i=0
    · subst i; simp [exchange,h01,Ne.symm h01]
    · by_cases hi1 : i=1
      · subst i; simp [exchange,h01,Ne.symm h01]
      · simp [exchange,hi0,hi1,Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  unfold compareHead
  have h0 : exchange d 0=d 1+1 := by simp [exchange,h01]
  have h1 : exchange d 1=d 0-1 := by simp [exchange,Ne.symm h01]
  rw [h0,h1,he]
  by_cases hlt : d 0 < d 1+1
  · rw [ite_eq_left (by omega),ite_eq_right (by omega)]
  · by_cases hgt : d 1+1 < d 0
    · rw [ite_eq_right (by omega),ite_eq_left hgt]
    · have heq : exchange d=d := by
        funext i
        by_cases hi0 : i=0
        · subst i; rw [h0]; omega
        · by_cases hi1 : i=1
          · subst i; rw [h1]; omega
          · simp [exchange,hi0,hi1,Equiv.swap_apply_of_ne_of_ne hi0 hi1]
      simp only [heq,ite_self]

theorem compare_rank_le_exchange (hn : 2 ≤ n) (d : Fin n → ℤ) :
    RankLE (compareHead d) (exchange d) := by
  rw [← compare_exchange_eq hn d]
  exact compare_rank_le_self hn _

theorem threshold_rank_zero_diagonal (r : Fin n) :
    thresholdRank (fun _ : Fin n => 0) r ((r : ℤ)+1)=0 := by
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  unfold thresholdRank
  apply Finset.sum_eq_zero
  intro i _
  by_cases hir : i ≤ r
  · have hq : ((i : ℤ)-((r : ℤ)+1))/(n : ℤ)= -1 := by
      apply LRX.PeriodicBuffer.quotient_eq_of_bounds hnpos <;> have := i.isLt <;>
        have := r.isLt <;> have : i.val ≤ r.val := hir <;> omega
    simp [targets,hir,hq]
  · have hq : ((i : ℤ)-((r : ℤ)+1))/(n : ℤ)=0 := by
      apply LRX.PeriodicBuffer.quotient_eq_of_bounds hnpos <;> have := i.isLt <;>
        have := r.isLt <;> have : ¬i.val ≤ r.val := hir <;> omega
    simp [targets,hir,hq]

/-- Dominance by the sorted board forces a balanced board to be zero.
This connects the rank order to literal completion, not just a statistic. -/
theorem zero_of_rank_le_zero (d : Fin n → ℤ) (hb : ∑ i,d i=0)
    (hle : RankLE d (fun _ => 0)) : ∀ i,d i=0 := by
  have hnonpos (i : Fin n) : d i ≤ 0 := by
    have hr := hle i ((i : ℤ)+1)
    rw [threshold_rank_zero_diagonal] at hr
    have ht := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => max ((targets d j-((i : ℤ)+1))/(n : ℤ)+(if j ≤ i then 1 else 0)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    change _ ≤ thresholdRank d i ((i : ℤ)+1) at ht
    simp only [le_refl,ite_true,targets] at ht
    have he : (i : ℤ)+d i-((i : ℤ)+1)=d i-1 := by ring
    rw [he] at ht
    by_contra hnot
    have hq := Int.ediv_nonneg (show 0 ≤ d i-1 by omega) (show (0 : ℤ) ≤ n by positivity)
    omega
  exact fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnonpos j)).mp hb i (Finset.mem_univ i)

#print axioms compare_threshold_rank_head
#print axioms compare_rank_mono
#print axioms zero_of_rank_le_zero
end LX.AffineScan
