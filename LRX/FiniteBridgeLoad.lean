import LRX.FiniteBridgeInversions

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem component_bridge_half_load (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val) (e : ℕ) :
    halfLoad (componentBridge p u v).symm e=halfLoad p.symm e+
      if u.val < e ∧ e ≤ v.val then 1 else 0 := by
  have hne : u ≠ v := by intro he; subst v; omega
  let A : ℕ := if u.val < e ∧ e ≤ (p.symm v).val then 1 else 0
  let B : ℕ := if v.val < e ∧ e ≤ (p.symm v).val then 1 else 0
  have point (i : Fin n) :
      (if i.val < e ∧ e ≤ ((componentBridge p u v).symm i).val then (1 : ℕ) else 0)+
        (if i=v then B else 0)=
      (if i.val < e ∧ e ≤ (p.symm i).val then 1 else 0)+(if i=u then A else 0) := by
    rw [component_bridge_inverse]
    by_cases hi : i=u
    · subst i
      simp only [Equiv.swap_apply_left,ite_true,ite_eq_right hne,add_zero,A]
      have hh : ¬(u.val < e ∧ e ≤ (p.symm u).val) := by omega
      simp only [hh,ite_false,zero_add]
    · by_cases hj : i=v
      · subst i
        simp only [Equiv.swap_apply_right,ite_eq_right hi,ite_true,add_zero,B]
        have hh : ¬(v.val < e ∧ e ≤ (p.symm u).val) := by omega
        simp only [hh,ite_false,zero_add]
      · simp only [Equiv.swap_apply_of_ne_of_ne hi hj,ite_eq_right hi,ite_eq_right hj,add_zero]
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  rw [← forward_as_sum,← forward_as_sum] at hs
  have hab : A=B+(if u.val < e ∧ e ≤ v.val then 1 else 0) := by
    dsimp [A,B]
    split_ifs <;> omega
  omega

theorem component_bridge_cut_load (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (e : ℕ) (he : e ≤ n) :
    cutLoad (componentBridge p u v).symm e=cutLoad p.symm e+
      if u.val < e ∧ e ≤ v.val then 2 else 0 := by
  rw [cut_load_eq_twice_half _ e he,cut_load_eq_twice_half _ e he,
    component_bridge_half_load p u v huv ha hb e]
  split_ifs <;> push_cast <;> ring

#print axioms component_bridge_half_load
#print axioms component_bridge_cut_load
end LRX.FiniteCuts
