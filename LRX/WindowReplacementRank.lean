import LRX.FiniteReversalRank
import LRX.WindowReplacement

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteRankOrder
variable {n b : ℕ}

theorem window_rank_indicator (W : Window n b) (f : State b) (k t : ℕ) (i : Fin b) :
    (if (embed W i).val < k ∧ t < (embed W (f i)).val then (1 : ℤ) else 0)=
      if t < W.offset then (if i.val < k-W.offset then 1 else 0)
      else (if i.val < k-W.offset ∧ t-W.offset < (f i).val then 1 else 0) := by
  dsimp [embed]
  split_ifs <;> omega

/-- A rank increase of the actual filling increases the whole ambient permutation. -/
theorem below_replace (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (hfg : Below f g) :
    Below p (replace W p f g) := by
  intro k t
  let D : Fin n → ℤ := fun i =>
    (if i.val < k ∧ t < (replace W p f g i).val then 1 else 0)-
    (if i.val < k ∧ t < (p i).val then 1 else 0)
  have hd : (rank (replace W p f g) k t : ℤ)-(rank p k t : ℤ)=∑ i, D i := by
    simp only [rank,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,D,Finset.sum_sub_distrib]
  have hout (i : Fin n) (hi : ¬Contains W i) : D i=0 := by
    dsimp [D]
    rw [replace_outside W p f g i hi]
    omega
  rw [sum_window W D hout] at hd
  have hpoint (i : Fin b) : D (embed W i)=
      (if t < W.offset then (if i.val < k-W.offset then (1 : ℤ) else 0)
        else (if i.val < k-W.offset ∧ t-W.offset < (g i).val then 1 else 0))-
      (if t < W.offset then (if i.val < k-W.offset then (1 : ℤ) else 0)
        else (if i.val < k-W.offset ∧ t-W.offset < (f i).val then 1 else 0)) := by
    dsimp [D]
    rw [replace_embed W p f g hmatch,hmatch,window_rank_indicator,window_rank_indicator]
  simp_rw [hpoint] at hd
  by_cases ht : t < W.offset
  · simp only [if_pos ht,sub_self,Finset.sum_const_zero] at hd
    omega
  · simp only [if_neg ht,Finset.sum_sub_distrib] at hd
    have hle : (rank f (k-W.offset) (t-W.offset) : ℤ) ≤
        (rank g (k-W.offset) (t-W.offset) : ℤ) := by exact_mod_cast hfg (k-W.offset) (t-W.offset)
    simp only [rank,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hle
    omega

/-- Reversal of an invariant block is an upper target for the original map. -/
theorem below_reversal_replacement (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) : Below p (replace W p f Fin.revPerm) :=
  below_replace W p f Fin.revPerm hmatch (below_reversal f)

#print axioms below_replace
#print axioms below_reversal_replacement
end LRX.FiniteWindow
