import LRX.FiniteCycleAvailability
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! Cut loads add across disjoint cycles. This identifies the aggregate load
with the cut load of the permutation, before choosing service ports. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem forward_mul_of_disjoint (p q : State b) (e : ℕ) (h : p.Disjoint q) :
    forward (p*q) e = forward p e ∪ forward q e := by
  ext i
  simp only [Finset.mem_union, mem_forward]
  rcases h i with hi | hi
  · have hm : (p*q) i = q i := by rw [h.commute.eq]; simp [hi]
    rw [hm, hi]
    omega
  · have hm : (p*q) i = p i := by simp [hi]
    rw [hm, hi]
    omega

theorem forward_disjoint (p q : State b) (e : ℕ) (h : p.Disjoint q) :
    Disjoint (forward p e) (forward q e) := by
  apply Finset.disjoint_left.mpr
  intro i hp hq
  have hp := (mem_forward p e i).mp hp
  have hq := (mem_forward q e i).mp hq
  rcases h i with hi | hi
  · rw [hi] at hp; omega
  · rw [hi] at hq; omega

theorem half_load_mul (p q : State b) (e : ℕ) (h : p.Disjoint q) :
    halfLoad (p*q) e = halfLoad p e + halfLoad q e := by
  unfold halfLoad
  rw [forward_mul_of_disjoint p q e h, Finset.card_union_of_disjoint (forward_disjoint p q e h)]

@[simp] theorem half_load_one (e : ℕ) : halfLoad (1 : State b) e = 0 := by
  have : forward (1 : State b) e = ∅ := by ext i; simp
  simp [halfLoad, this]

theorem half_load_list_prod (l : List (State b)) (h : l.Pairwise Equiv.Perm.Disjoint)
    (e : ℕ) : halfLoad l.prod e = (l.map (fun p => halfLoad p e)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hp, hl⟩ := List.pairwise_cons.mp h
    have hd : p.Disjoint l.prod := Equiv.Perm.disjoint_prod_right l hp
    simpa using (half_load_mul p l.prod e hd).trans (by rw [ih hl])

theorem half_load_cycle_sum (p : State b) (e : ℕ) :
    halfLoad p e = ∑ q ∈ p.cycleFactorsFinset, halfLoad q e := by
  classical
  obtain ⟨l, hn, heq⟩ := p.cycleFactorsFinset.exists_list_nodup_eq
  have h := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hn).mp heq.symm
  calc
    halfLoad p e = halfLoad l.prod e := by rw [h.2.2]
    _ = (l.map (fun q => halfLoad q e)).sum := half_load_list_prod l h.2.1 e
    _ = ∑ q ∈ l.toFinset, halfLoad q e := (List.sum_toFinset _ hn).symm
    _ = _ := by rw [heq]

#print axioms half_load_cycle_sum
end LRX.FiniteCuts
