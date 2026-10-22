import LX.ForwardPrefixContraction
import LRX.FiniteInversionBalance

namespace LX.FiniteDropBudget
open scoped BigOperators
open LRX.FiniteCuts
variable {k : ℕ}

theorem rotate_conjugate_drops (p : LRX.State (k+1)) (hp : p 0 ≠ 0) :
    (descendingPositions (rotateConjugate p)).card=(descendingPositions p).card := by
  have hp' : p.symm 0 ≠ 0 := by
    intro he
    have hh := congrArg p he
    simp only [Equiv.apply_symm_apply] at hh
    exact hp hh.symm
  have hz (i : Fin (k+1)) : p i=0 ↔ i=p.symm 0 := by
    exact (Equiv.eq_symm_apply p).symm
  have hpoint (i : Fin (k+1)) :
      descendingIndicator (rotateConjugate p) ((finRotate (k+1)).symm i)+
        (if i=p.symm 0 then (1 : ℤ) else 0)=
      descendingIndicator p i+(if i=0 then (1 : ℤ) else 0) := by
    have hri := inverse_rotate_int i
    have hrp := inverse_rotate_int (p i)
    have he : rotateConjugate p ((finRotate (k+1)).symm i)=
        (finRotate (k+1)).symm (p i) := by
      simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply]
    unfold descendingIndicator
    rw [he]
    simp only [hz] at hrp
    by_cases hi0 : i=0
    · subst i
      simp only [hp',Ne.symm hp',ite_false,ite_true,Fin.val_zero,Nat.cast_zero] at hri hrp ⊢
      have := (p 0).isLt
      have := Fin.pos_iff_ne_zero.mpr hp
      split_ifs <;> omega
    by_cases hip : i=p.symm 0
    · subst i
      simp only [hp',ite_false,ite_true,Equiv.apply_symm_apply,Fin.val_zero,Nat.cast_zero] at hri hrp ⊢
      have := (p.symm 0).isLt
      have := Fin.pos_iff_ne_zero.mpr hp'
      split_ifs <;> omega
    · simp only [hi0,hip,ite_false,add_zero] at hri hrp ⊢
      split_ifs <;> omega
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  rw [Equiv.sum_comp (finRotate (k+1)).symm,sum_descending_indicator,sum_descending_indicator] at hs
  omega

theorem rotate_conjugate_units_le (p : LRX.State (k+1))
    (hp : p 0 ≠ Fin.last k) :
    (backwardUnits (rotateConjugate p)).card ≤ (backwardUnits p).card := by
  classical
  apply Finset.card_le_card_of_injOn (finRotate (k+1))
  · intro j hj
    let i := finRotate (k+1) j
    have hj' : j=(finRotate (k+1)).symm i := by simp [i]
    have hunit : ((rotateConjugate p) j).val+1=j.val := (Finset.mem_filter.mp hj).2
    have he : rotateConjugate p j=(finRotate (k+1)).symm (p i) := by
      simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,i]
    have hri := inverse_rotate_int i
    have hrp := inverse_rotate_int (p i)
    rw [he,hj'] at hunit
    have hi := i.isLt
    have hpi := (p i).isLt
    have hval : (p 0).val ≠ k := fun hh => hp (Fin.ext hh)
    have hgoal : (p i).val+1=i.val := by
      by_cases hi0 : i=0
      · simp only [hi0,ite_true,Fin.val_zero,Nat.cast_zero] at hri hrp hunit ⊢
        split_ifs at hrp <;> omega
      by_cases hpi0 : p i=0
      · simp only [hpi0,hi0,ite_false,ite_true,Fin.val_zero,Nat.cast_zero,add_zero] at hri hrp hunit
        omega
      · simp only [hi0,hpi0,ite_false,add_zero] at hri hrp
        omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgoal⟩
  · intro i _ j _ he
    exact (finRotate (k+1)).injective he

/-- A fixed interval just after a moving head can be recentered without
creating a backward unit arrow unless the head maps to the last position. -/
theorem fixed_middle_drop_bound (p : LRX.State (k+1)) (r : ℕ)
    (hr : r ≤ k+1) (hp : p 0 ≠ 0) (hlast : p 0 ≠ Fin.last k)
    (hfix : ∀ i : Fin (k+1),0 < i.val → i.val < r → p i=i) :
    3*((descendingPositions p).card : ℤ) ≤ ((k+1 : ℕ) : ℤ)-(r : ℤ)+
      (∑ i, |displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card := by
  have h := fixed_prefix_drop_bound (rotateConjugate p) (r-1) (by omega) (by
    intro i hi
    have hik : i.val < k := by omega
    have hri : (finRotate (k+1) i).val=i.val+1 := by
      rw [finRotate_of_lt hik]
    have hf := hfix (finRotate (k+1) i) (by omega) (by omega)
    simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,hf,Equiv.symm_apply_apply])
  rw [rotate_conjugate_drops p hp] at h
  have hm := rotation_energy_minus_inversions p
  have hu := rotate_conjugate_units_le p hlast
  rw [Nat.cast_sub (by omega : r-1 ≤ k+1)] at h
  omega

#print axioms rotate_conjugate_drops
#print axioms rotate_conjugate_units_le
#print axioms fixed_middle_drop_bound
end LX.FiniteDropBudget
