import LRX.NestedMatchingGeometry

namespace LRX.FiniteCuts
variable {n : ℕ}

/-- Counting the two exterior regions identifies the sum of a nested pair's endpoints. -/
theorem nested_pair_endpoint_sum (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hsep : NoSeparatedPairs p) (hfixed : ∀ i, p i ≠ i)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) : a.val+b.val=n-1 := by
  have hcard : (Finset.Iio a).card=(Finset.Ioi b).card := by
    refine Finset.card_bij (fun x _ => p x) ?_ ?_ ?_
    · intro x hx
      have hlt : x<a := Finset.mem_Iio.mp hx
      apply Finset.mem_Ioi.mpr
      exact (nested_pair_exterior p hinv hnc hsep hfixed a b hab hpab x).1 hlt
    · intro x hx y hy heq
      exact p.injective heq
    · intro y hy
      refine ⟨p y,?_,hinv y⟩
      have hlt : b<y := Finset.mem_Ioi.mp hy
      apply Finset.mem_Iio.mpr
      exact (nested_pair_exterior p hinv hnc hsep hfixed a b hab hpab y).2 hlt
  rw [Fin.card_Iio,Fin.card_Ioi] at hcard
  have hb := b.isLt
  omega

/-- A fixed-point-free noncrossing matching with at most one adjacent pair is reversal. -/
theorem unique_adjacent_matching_reflection (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hfixed : ∀ i, p i ≠ i)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin n, p i=i.rev := by
  have hsep := no_separated_pairs_of_unique_adjacent p hinv hnc hfixed hunique
  intro i
  have hne : (p i).val ≠ i.val := fun h => hfixed i (Fin.ext h)
  have hsum : i.val+(p i).val=n-1 := by
    by_cases hlt : i.val < (p i).val
    · exact nested_pair_endpoint_sum p hinv hnc hsep hfixed i (p i) hlt rfl
    · have h := nested_pair_endpoint_sum p hinv hnc hsep hfixed (p i) i (by omega) (hinv i)
      omega
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

#print axioms nested_pair_endpoint_sum
#print axioms unique_adjacent_matching_reflection
end LRX.FiniteCuts
