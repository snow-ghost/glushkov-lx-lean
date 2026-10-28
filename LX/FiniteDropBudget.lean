import LX.FiniteDescentRank
import LX.FiniteInversionRotation
import LX.FiniteWindowRestriction
import Mathlib

namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts

def backwardUnits {n : ℕ} (p : LX.Core.State n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (p i).val+1=i.val

theorem forward_rotate_int {k : ℕ} (i : Fin (k+1)) :
    (finRotate (k+1) i : ℤ)=(i : ℤ)+1-
      if i=Fin.last k then (k+1 : ℤ) else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [rotate_castSucc]
    simp

theorem forward_mass_change {k : ℕ} (p : LX.Core.State (k+1)) :
    (∑ i, |displacement (finRotate (k+1)*p) i|)=
      (∑ i, |displacement p i|)+2*(p.symm (Fin.last k) : ℤ)-
        2*(descendingPositions p).card := by
  classical
  have hpoint (i : Fin (k+1)) :
      |displacement (finRotate (k+1)*p) i|=|displacement p i|+1-
        2*(if (p i).val < i.val then (1 : ℤ) else 0)+
        (if i=p.symm (Fin.last k) then 2*(i : ℤ)-(k+1 : ℤ) else 0) := by
    have he : p i=Fin.last k ↔ i=p.symm (Fin.last k) :=
      (Equiv.eq_symm_apply p).symm
    simp only [displacement,Equiv.Perm.mul_apply,forward_rotate_int,he]
    have hi := i.isLt
    have hp := (p i).isLt
    by_cases hm : i=p.symm (Fin.last k)
    · have hv := congrArg Fin.val (he.mpr hm)
      simp only [Fin.val_last] at hv
      rw [ite_eq_left hm]
      split_ifs <;> rw [abs_eq_max_neg,abs_eq_max_neg] <;> omega
    · rw [ite_eq_right hm]
      simp only [sub_zero]
      split_ifs <;> rw [abs_eq_max_neg,abs_eq_max_neg] <;> omega
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.mul_sum]
  have hc : (∑ i : Fin (k+1),if (p i).val < i.val then (1 : ℤ) else 0)=
      ((descendingPositions p).card : ℤ) := by simp [descendingPositions]
  rw [hc]
  push_cast
  ring

/-- Rotating the values gives a drop-count bound with the exact number of
backward unit arrows. No shallow or minimum-phase assumption is needed. -/
theorem three_drops_bound {k : ℕ} (p : LX.Core.State (k+1)) :
    3*((descendingPositions p).card : ℤ) ≤ (k+1 : ℤ)+
      (∑ i, |displacement p i|)-(inversionNumber p : ℤ)+
        (backwardUnits p).card-1 := by
  classical
  let q := finRotate (k+1)*p
  have hi := value_rotation_inversions q
  have he : (finRotate (k+1))⁻¹*q=p := by dsimp [q]; simp
  have hz : q⁻¹ 0=p.symm (Fin.last k) := by
    apply q.injective
    simp [q,Equiv.Perm.mul_apply]
  rw [he,hz] at hi
  have hm := forward_mass_change p
  have hd := finite_depth_descending q
  have hsubset : descendingPositions p ⊆ descendingPositions q ∪ backwardUnits p := by
    intro i hi
    have hpi := (mem_descendingPositions p i).mp hi
    by_cases hu : (p i).val+1=i.val
    · exact Finset.mem_union_right _ (by simp [backwardUnits,hu])
    · apply Finset.mem_union_left
      rw [mem_descendingPositions]
      have hp : (p i).val < k := by have := i.isLt; omega
      have hrot := finRotate_of_lt hp
      change (finRotate (k+1) (p i)).val < i.val
      rw [hrot]
      change (p i).val+1 < i.val
      omega
  have hc := (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hi' : (inversionNumber p : ℤ)+2*(p.symm (Fin.last k) : ℤ)=
      (inversionNumber q : ℤ)+k := by exact_mod_cast hi
  change (∑ i, |displacement q i|)=_ at hm
  have hc' : ((descendingPositions p).card : ℤ) ≤
      (descendingPositions q).card+(backwardUnits p).card := by exact_mod_cast hc
  linarith

#print axioms three_drops_bound

theorem three_drops_bound_of_pos {n : ℕ} (p : LX.Core.State n) (hn : 0 < n) :
    3*((descendingPositions p).card : ℤ) ≤ (n : ℤ)+
      (∑ i, |displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card-1 := by
  cases n with
  | zero => omega
  | succ k => simpa only [Nat.cast_add,Nat.cast_one] using three_drops_bound p

theorem window_stat_count {n b : ℕ} (W : LX.Core.FiniteWindow.Window n b)
    (p : LX.Core.State b) (P : ℤ → Prop) [DecidablePred P] (hP : ¬P 0) :
    (Finset.univ.filter fun i => P (displacement (LX.Core.FiniteWindow.permutation W p) i)).card=
      (Finset.univ.filter fun i => P (displacement p i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [LX.Core.FiniteWindow.sum_window_nat W _ (by
    intro i hi
    rw [LX.Core.FiniteWindow.displacement_outside W p i hi,ite_eq_right hP])]
  simp only [LX.Core.FiniteWindow.displacement_embed]

/-- A fixed initial interval can be removed before applying the drop budget.
All finite statistics are transferred through the actual tail restriction. -/
theorem fixed_prefix_drop_bound {n : ℕ} (p : LX.Core.State n) (r : ℕ) (hr : r < n)
    (hfix : ∀ i : Fin n,i.val < r → p i=i) :
    3*((descendingPositions p).card : ℤ) ≤ ((n-r : ℕ) : ℤ)+
      (∑ i, |displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card-1 := by
  classical
  let W : LX.Core.FiniteWindow.Window n (n-r) := ⟨r,by omega⟩
  have hW (i : Fin n) : LX.Core.FiniteWindow.Contains W (p i) ↔
      LX.Core.FiniteWindow.Contains W i := by
    change (r ≤ (p i).val ∧ (p i).val < r+(n-r)) ↔
      (r ≤ i.val ∧ i.val < r+(n-r))
    have hi := i.isLt
    have hp := (p i).isLt
    have hsmall : (p i).val < r ↔ i.val < r := by
      constructor
      · intro h
        have he : p i=i := p.injective (hfix (p i) h)
        rwa [he] at h
      · intro h
        rwa [hfix i h]
    omega
  let q := LX.Core.FiniteWindow.restriction W p hW
  have he : LX.Core.FiniteWindow.permutation W q=p := by
    apply Equiv.ext
    intro i
    by_cases hi : LX.Core.FiniteWindow.Contains W i
    · obtain ⟨j,rfl⟩ := (LX.Core.FiniteWindow.contains_iff W i).mp hi
      rw [LX.Core.FiniteWindow.permutation_embed]
      exact LX.Core.FiniteWindow.embed_restriction W p hW j
    · rw [LX.Core.FiniteWindow.permutation_outside W q i hi]
      apply (hfix i _).symm
      have hit := i.isLt
      change ¬(r ≤ i.val ∧ i.val < r+(n-r)) at hi
      omega
  have hdesc := window_stat_count W q (fun z => z < 0) (by omega)
  have hu := window_stat_count W q (fun z => z = -1) (by omega)
  rw [he] at hdesc hu
  have hd (m : ℕ) (s : LX.Core.State m) :
      (Finset.univ.filter fun i => displacement s i < 0)=descendingPositions s := by
    unfold descendingPositions
    apply Finset.filter_congr
    intro i _
    unfold displacement
    omega
  have hb (m : ℕ) (s : LX.Core.State m) :
      (Finset.univ.filter fun i => displacement s i = -1)=backwardUnits s := by
    unfold backwardUnits
    apply Finset.filter_congr
    intro i _
    unfold displacement
    omega
  rw [hd,hd] at hdesc
  rw [hb,hb] at hu
  have hm := LX.Core.FiniteWindow.displacement_mass W q
  have hi := LX.Core.FiniteWindow.inversion_number_window W q
  rw [he] at hm hi
  have hbound := three_drops_bound_of_pos q (by omega : 0 < n-r)
  rwa [← hdesc,← hu,← hm,← hi] at hbound

#print axioms fixed_prefix_drop_bound
end LX.FiniteDropBudget
