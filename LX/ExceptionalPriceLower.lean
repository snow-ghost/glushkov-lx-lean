import LX.BoundedGreedyNormalForm
import LX.ExceptionalPrefixDelay
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem sum_depth_eq_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) : ∑ i,backwardDepth d i=inversions d := by
  have hh := LX.Core.RotationWords.twice_inversion_count hd
  have he : (∑ i : Fin n,∑ j : Fin n,(LX.Core.AffineLift.crossing d i j).toNat)=
      ∑ i : Fin n,∑ j : Fin n,(-LX.Core.AffineLift.crossing d i j).toNat := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [LX.Core.AffineLift.crossing_antisymm hd j i]
  simp_rw [← Int.toNat_add_toNat_neg_eq_natAbs,Finset.sum_add_distrib] at hh
  rw [he] at hh
  change 2*inversions d=(∑ i,backwardDepth d i)+(∑ i,backwardDepth d i) at hh
  omega

/-- A descending interval contributes its earlier positions to depth. -/
theorem interval_depth_lower (d : Fin n → ℤ) (a i : Fin n)
    (ht : ∀ j : Fin n,a ≤ j → j < i → targets d i ≤ targets d j) :
    i.val-a.val ≤ backwardDepth d i := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hp (j : Fin n) : (if a ≤ j ∧ j < i then 1 else 0) ≤
      ((targets d j-targets d i)/(n : ℤ)+if j < i then 1 else 0).toNat := by
    split_ifs with hj hji hji
    · have hq := Int.ediv_nonneg (show 0 ≤ targets d j-targets d i by have := ht j hj.1 hj.2; omega)
        (le_of_lt hn)
      omega
    · exact False.elim (hji hj.2)
    · omega
    · omega
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp j)
  have hset : (Finset.univ.filter fun j : Fin n => a ≤ j ∧ j < i)=Finset.Ico a i := by ext; simp
  convert hs using 1 <;>
    simp only [Finset.sum_boole,hset,Fin.card_Ico,← backward_depth_formula] <;> rfl

def evenDepthLower (m k : ℕ) : ℕ :=
  if k=0 then m-2 else if k ≤ 2 then m-1 else if k ≤ m+1 then k-3 else k-(m+2)

def oddDepthLower (m k : ℕ) : ℕ :=
  if k=0 then m-1 else if k=1 then m else if k=2 then 0
  else if k ≤ m+1 then k-3 else k-(m+2)

theorem even_exception_depth_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m))
    (i : Fin n) : evenDepthLower m i.val ≤ backwardDepth (evenException m) i := by
  have hil := i.isLt
  unfold evenDepthLower
  split_ifs with hi0 hi2 hiM
  · have hi : i=0 := Fin.ext hi0
    subst i
    have hh := tail_head_depth_lower (evenException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro j hj
      have hjl := j.isLt
      have hjp : m+2 ≤ j.val := hj
      simp only [targets,evenException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
        ite_eq_right (by omega : ¬j.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-2 by omega] using hh
  · have hh := neg_displacement_le_depth hd i
    simp only [evenException,ite_eq_right hi0,ite_eq_left hi2] at hh
    omega
  · apply interval_depth_lower (evenException m) (⟨3,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : 3 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,evenException,ite_eq_right hi0,ite_eq_right hi2,ite_eq_left hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
      ite_eq_left (by omega : j.val ≤ m+1)]
    omega
  · apply interval_depth_lower (evenException m) (⟨m+2,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : m+2 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,evenException,ite_eq_right hi0,ite_eq_right hi2,ite_eq_right hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
      ite_eq_right (by omega : ¬j.val ≤ m+1)]
    omega

theorem odd_exception_depth_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m))
    (i : Fin n) : oddDepthLower m i.val ≤ backwardDepth (oddException m) i := by
  have hil := i.isLt
  unfold oddDepthLower
  split_ifs with hi0 hi1 hi2 hiM
  · have hi : i=0 := Fin.ext hi0
    subst i
    have hh := tail_head_depth_lower (oddException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro j hj
      have hjl := j.isLt
      have hjp : m+2 ≤ j.val := hj
      simp only [targets,oddException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
        ite_eq_right (by omega : j.val ≠ 2),ite_eq_right (by omega : ¬j.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-1 by omega] using hh
  · have hh := neg_displacement_le_depth hd i
    simp only [oddException,ite_eq_right hi0,ite_eq_left hi1] at hh
    omega
  · exact Nat.zero_le _
  · apply interval_depth_lower (oddException m) (⟨3,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : 3 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,oddException,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,
      ite_eq_left hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
      ite_eq_right (by omega : j.val ≠ 2),ite_eq_left (by omega : j.val ≤ m+1)]
    omega
  · apply interval_depth_lower (oddException m) (⟨m+2,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : m+2 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,oddException,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,
      ite_eq_right hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
      ite_eq_right (by omega : j.val ≠ 2),ite_eq_right (by omega : ¬j.val ≤ m+1)]
    omega

omit [NeZero n] in
theorem even_depth_lower_sum (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    ∑ i : Fin n,evenDepthLower m i.val=m*(m-1) := by
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-2) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,evenDepthLower m k)=(m-2)+2*(m-1) := by
    norm_num [Finset.sum_range_succ,evenDepthLower]
    omega
  have hmid : (∑ k ∈ Finset.range (m-1),evenDepthLower m (3+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold evenDepthLower
    split_ifs <;> omega
  have htail : (∑ k ∈ Finset.range (m-2),evenDepthLower m (3+(m-1)+k))=
      ∑ k ∈ Finset.range (m-2),k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold evenDepthLower
    split_ifs <;> omega
  rw [hfirst,hmid,htail]
  have hs1 := Finset.sum_range_id_mul_two (m-1)
  have hs2 := Finset.sum_range_id_mul_two (m-2)
  have hm1 : m-1+1=m := by omega
  have hm2 : m-2+2=m := by omega
  have hm3 : m-2-1+3=m := by omega
  have he : m-1-1=m-2 := by omega
  rw [he] at hs1
  nlinarith

omit [NeZero n] in
theorem odd_depth_lower_sum (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    ∑ i : Fin n,oddDepthLower m i.val=m*(m-1)+1 := by
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-1) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,oddDepthLower m k)=(m-1)+m := by
    norm_num [Finset.sum_range_succ,oddDepthLower]
  have hmid : (∑ k ∈ Finset.range (m-1),oddDepthLower m (3+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold oddDepthLower
    split_ifs <;> omega
  have htail : (∑ k ∈ Finset.range (m-1),oddDepthLower m (3+(m-1)+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold oddDepthLower
    split_ifs <;> omega
  rw [hfirst,hmid,htail]
  have hs1 := Finset.sum_range_id_mul_two (m-1)
  have hm1 : m-1+1=m := by omega
  have hm2 : m-1-1+2=m := by omega
  nlinarith

theorem even_exception_inversions_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m)) :
    m*(m-1) ≤ inversions (evenException (n := n) m) := by
  rw [← sum_depth_eq_inversions hd,← even_depth_lower_sum m hm hn]
  exact Finset.sum_le_sum (fun i _ => even_exception_depth_lower m hm hn hd i)

theorem odd_exception_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m)) :
    m*(m-1)+1 ≤ inversions (oddException (n := n) m) := by
  rw [← sum_depth_eq_inversions hd,← odd_depth_lower_sum m hm hn]
  exact Finset.sum_le_sum (fun i _ => odd_exception_depth_lower m hm hn hd i)

/-- The exceptional even lift cannot beat the conjectured diameter price.
The statement concerns this lift, not every lift of the antipode. -/
theorem even_exception_price_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m))
    {g : List Letter} (hg : ScanTrace (evenException (n := n) m) g) :
    3*m^2-4*m+3 ≤ inversions (evenException (n := n) m)+paidRotations ((m+3 : ℕ) : Fin n) g := by
  have hI := even_exception_inversions_lower m hm hn hd
  have hL := even_exception_paid_rotation_lower m hm hn hd hg
  have hm1 : m-1+1=m := by omega
  have hm2 : m-2+2=m := by omega
  have hn1 : n-1+1=n := by omega
  have he : 4*m ≤ 3*m^2 := by nlinarith
  have hsub := Nat.sub_add_cancel he
  nlinarith

/-- The odd exceptional lift is at least one unit more expensive than the
conjectured diameter, so it cannot be a missing cheaper representation. -/
theorem odd_exception_price_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m))
    {g : List Letter} (hg : ScanTrace (oddException (n := n) m) g) :
    3*m^2-m+2 ≤ inversions (oddException (n := n) m)+paidRotations ((m+2 : ℕ) : Fin n) g := by
  have hI := odd_exception_inversions_lower m hm hn hd
  have hL := odd_exception_paid_rotation_lower m hm hn hd hg
  have hm1 : m-1+1=m := by omega
  have hn1 : n-1+1=n := by omega
  have he : m ≤ 3*m^2 := by nlinarith
  have hsub := Nat.sub_add_cancel he
  nlinarith


#print axioms sum_depth_eq_inversions
#print axioms even_exception_depth_lower
#print axioms odd_exception_depth_lower
#print axioms even_exception_price_lower
#print axioms odd_exception_price_lower
end LX.AffineScan
