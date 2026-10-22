import LRX.FiniteRankOrder

namespace LRX.FiniteRankOrder
open scoped BigOperators
variable {n : ℕ}

theorem rank_succ (p : State n) (a : Fin n) (t : ℕ) :
    rank p (a.val+1) t=rank p a.val t+(if t<(p a).val then 1 else 0) := by
  classical
  unfold rank
  calc
    _ = ∑ i : Fin n, ((if i.val<a.val ∧ t<(p i).val then 1 else 0)+
        if i=a then (if t<(p a).val then 1 else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hia : i=a
      · subst i; simp
      · have hv : i.val ≠ a.val := fun h => hia (Fin.ext h)
        by_cases hlt : i.val<a.val <;> by_cases ht : t<(p i).val <;>
          simp [hia,hlt,ht,show (i.val<a.val+1) ↔ i.val<a.val by omega]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

noncomputable def compareAt (p : State n) (a b : Fin n) : State n :=
  if (p a).val ≤ (p b).val then p else p*Equiv.swap a b

theorem rank_compare_away (p : State n) (a b : Fin n) (hab : b.val=a.val+1)
    (k t : ℕ) (hk : k ≠ b.val) : rank (compareAt p a b) k t=rank p k t := by
  classical
  unfold compareAt
  split_ifs with hp
  · rfl
  · have h := rank_swap p a b (by intro he; subst b; omega) k t
    have habk : a.val<k ↔ b.val<k := by omega
    by_cases ha : a.val<k <;> by_cases hb : b.val<k <;>
      by_cases hpa : t<(p a).val <;> by_cases hpb : t<(p b).val <;>
      simp [ha,hb,hpa,hpb] at h <;> omega

theorem rank_compare_middle (p : State n) (a b : Fin n) (hab : b.val=a.val+1) (t : ℕ) :
    rank (compareAt p a b) b.val t = rank p a.val t+
      min (if t<(p a).val then 1 else 0) (if t<(p b).val then 1 else 0) := by
  classical
  have hpre := rank_compare_away p a b hab a.val t (by omega)
  have hsucc := rank_succ (compareAt p a b) a t
  rw [← hab,hpre] at hsucc
  rw [hsucc]
  congr 1
  unfold compareAt
  by_cases hp : (p a).val ≤ (p b).val <;>
    simp only [hp,ite_true,ite_false,Equiv.Perm.mul_apply,Equiv.swap_apply_left] <;>
    by_cases hpa : t<(p a).val <;> by_cases hpb : t<(p b).val <;>
      simp [hpa,hpb] <;> omega

/-- Applying the same adjacent comparator preserves every prefix rank bound. -/
theorem below_compare (p q : State n) (hpq : Below p q)
    (a b : Fin n) (hab : b.val=a.val+1) :
    Below (compareAt p a b) (compareAt q a b) := by
  intro k t
  by_cases hk : k=b.val
  · subst k
    rw [rank_compare_middle p a b hab,rank_compare_middle q a b hab]
    have h0 := hpq a.val t
    have h1 := hpq b.val t
    have h2 := hpq (b.val+1) t
    have hp1 := rank_succ p a t
    have hq1 := rank_succ q a t
    rw [← hab] at hp1 hq1
    rw [rank_succ p b,rank_succ q b,hp1,hq1] at h2
    rw [hp1,hq1] at h1
    by_cases hpa : t<(p a).val <;> by_cases hpb : t<(p b).val <;>
      by_cases hqa : t<(q a).val <;> by_cases hqb : t<(q b).val <;>
      simp [hpa,hpb,hqa,hqb] at h1 h2 ⊢ <;> omega
  · rw [rank_compare_away p a b hab k t hk,rank_compare_away q a b hab k t hk]
    exact hpq k t

#print axioms rank_succ
#print axioms below_compare
end LRX.FiniteRankOrder
