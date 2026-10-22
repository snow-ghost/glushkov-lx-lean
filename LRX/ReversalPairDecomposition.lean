import LRX.PairExactCost

namespace LRX.FiniteCuts
variable {n : ℕ}

def reversalLeft (i : Fin (n/2)) : Fin n := ⟨i.val,by have := i.isLt; omega⟩

def reversalPair (i : Fin (n/2)) : State n := Equiv.swap (reversalLeft i) (reversalLeft i).rev

def reversalPairs (n : ℕ) : List (State n) := List.ofFn (fun i : Fin (n/2) => reversalPair i)

theorem reversal_left_lt_right (i : Fin (n/2)) : (reversalLeft i).val < (reversalLeft i).rev.val := by
  have hi := i.isLt
  simp only [reversalLeft,Fin.val_rev]
  omega

theorem reversal_pairs_disjoint (i j : Fin (n/2)) (hij : i ≠ j) :
    (reversalPair i).Disjoint (reversalPair j) := by
  have hi := i.isLt
  have hj := j.isLt
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  apply Equiv.Perm.disjoint_swap_swap
  simp only [List.nodup_cons,List.mem_cons,List.mem_nil_iff,or_false,not_or,
    List.nodup_nil,and_true,Fin.ext_iff,reversalLeft,Fin.val_rev]
  refine ⟨⟨?_,hne,?_⟩,⟨?_,?_⟩,?_,by simp⟩ <;> omega

theorem reversal_pairs_pairwise (n : ℕ) : (reversalPairs n).Pairwise Equiv.Perm.Disjoint := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact reversal_pairs_disjoint i j (ne_of_lt hij)

theorem permutation_product_fixes (l : List (State n)) (x : Fin n)
    (hfix : ∀ p ∈ l, p x=x) : l.prod x=x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp := hfix p (by simp)
    have hl := ih (fun q hq => hfix q (by simp [hq]))
    simp only [List.prod_cons,Equiv.Perm.mul_apply,hl,hp]

/-- The indexed disjoint pairs multiply to the actual finite reversal. -/
theorem reversal_pairs_product (n : ℕ) : (reversalPairs n).prod=Fin.revPerm := by
  apply Equiv.ext
  intro x
  have hdis := reversal_pairs_pairwise n
  by_cases hx : x.val < n/2
  · let i : Fin (n/2) := ⟨x.val,hx⟩
    have hl : reversalLeft i=x := by apply Fin.ext; rfl
    have hm : reversalPair i ∈ reversalPairs n := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hn := reversal_left_lt_right i
    have hs : x ∈ (reversalPair i).support := by
      apply Equiv.Perm.mem_support.mpr
      simp only [reversalPair,hl,Equiv.swap_apply_left]
      intro h
      have hv := congrArg Fin.val h
      rw [hl] at hn
      omega
    have he := Equiv.Perm.eq_on_support_mem_disjoint hm hdis x hs
    simpa only [reversalPair,hl,Equiv.swap_apply_left,Fin.revPerm_apply] using he.symm
  · by_cases hr : x.rev.val < n/2
    · let i : Fin (n/2) := ⟨x.rev.val,hr⟩
      have hl : reversalLeft i=x.rev := by apply Fin.ext; rfl
      have hm : reversalPair i ∈ reversalPairs n := List.mem_ofFn.mpr ⟨i,rfl⟩
      have hn := reversal_left_lt_right i
      have hs : x ∈ (reversalPair i).support := by
        apply Equiv.Perm.mem_support.mpr
        simp only [reversalPair,hl,Fin.rev_rev,Equiv.swap_apply_right]
        intro h
        have hv := congrArg Fin.val h
        rw [hl,Fin.rev_rev] at hn
        omega
      have he := Equiv.Perm.eq_on_support_mem_disjoint hm hdis x hs
      simpa only [reversalPair,hl,Fin.rev_rev,Equiv.swap_apply_right,Fin.revPerm_apply] using he.symm
    · have hmid : x.rev=x := by
        apply Fin.ext
        have hxn := x.isLt
        simp only [Fin.val_rev] at hr ⊢
        omega
      have hp : (reversalPairs n).prod x=x := by
        apply permutation_product_fixes
        intro p hp
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          have hi := i.isLt
          have hv := congrArg Fin.val h
          change x.val=i.val at hv
          omega
        · intro h
          have hi := i.isLt
          have he := congrArg Fin.rev h
          simp only [Fin.rev_rev,hmid] at he
          have hv := congrArg Fin.val he
          change x.val=i.val at hv
          omega
      simpa only [Fin.revPerm_apply,hmid] using hp

#print axioms reversal_pairs_product
end LRX.FiniteCuts
