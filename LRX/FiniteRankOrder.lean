import LRX.Graph

/-! Prefix rank counts for finite target maps. Prefix lengths are natural
numbers, so the empty prefix is included without a fictitious negative index. -/
namespace LRX.FiniteRankOrder
open scoped BigOperators
variable {n : ℕ}

noncomputable def rank (p : State n) (k t : ℕ) : ℕ :=
  ∑ i : Fin n, if i.val < k ∧ t < (p i).val then 1 else 0

def Below (p q : State n) : Prop := ∀ k t, rank p k t ≤ rank q k t

theorem below_refl (p : State n) : Below p p := fun _ _ => le_rfl

theorem below_trans {p q r : State n} (hpq : Below p q) (hqr : Below q r) :
    Below p r := fun k t => (hpq k t).trans (hqr k t)

theorem sum_change_two (f g : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ i, i ≠ a → i ≠ b → f i=g i) :
    (∑ i, g i)+f a+f b=(∑ i, f i)+g a+g b := by
  classical
  let S := (Finset.univ.erase a).erase b
  have hs : ∑ i ∈ S, f i=∑ i ∈ S, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    exact h i (Finset.mem_erase.mp hi'.2).1 hi'.1
  have hf1 := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ a)
  have hg1 := Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ a)
  have hb : b ∈ Finset.univ.erase a := by simp [Ne.symm hab]
  have hf2 := Finset.sum_erase_add (s := Finset.univ.erase a) f hb
  have hg2 := Finset.sum_erase_add (s := Finset.univ.erase a) g hb
  dsimp [S] at hs
  omega

theorem rank_swap (p : State n) (a b : Fin n) (hab : a ≠ b) (k t : ℕ) :
    rank (p*Equiv.swap a b) k t+
      (if a.val<k ∧ t<(p a).val then 1 else 0)+
      (if b.val<k ∧ t<(p b).val then 1 else 0) =
    rank p k t+
      (if a.val<k ∧ t<(p b).val then 1 else 0)+
      (if b.val<k ∧ t<(p a).val then 1 else 0) := by
  classical
  have h := sum_change_two
    (fun i : Fin n => if i.val<k ∧ t<(p i).val then 1 else 0)
    (fun i : Fin n => if i.val<k ∧ t<((p*Equiv.swap a b) i).val then 1 else 0)
    a b hab (by
      intro i hia hib
      simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hia hib])
  simpa only [rank,Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using h

/-- Swapping two increasing values at increasing positions raises all ranks.
This is the comparison needed for an individual component bridge. -/
theorem below_raising_swap (p : State n) (a b : Fin n) (hab : a.val < b.val)
    (hvalues : (p a).val ≤ (p b).val) : Below p (p*Equiv.swap a b) := by
  intro k t
  have h := rank_swap p a b (by intro he; subst b; omega) k t
  by_cases ha : a.val<k <;> by_cases hb : b.val<k <;>
    by_cases hpa : t<(p a).val <;> by_cases hpb : t<(p b).val <;>
    simp only [ha,hb,hpa,hpb,and_self,ite_true,ite_false,and_false,false_and,true_and] at h <;> omega

#print axioms rank_swap
#print axioms below_raising_swap
end LRX.FiniteRankOrder
