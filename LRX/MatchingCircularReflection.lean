import LRX.TwoFixedMatchingReflection

namespace LRX.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem circular_reflection_of_endpoint_sum [NeZero n] (p : State n)
    (hzero : p 0=0) (hsum : ∀ i : Fin n, i ≠ 0 → i.val+(p i).val=n) :
    ∀ i, p i= -i := by
  intro i
  by_cases hi : i=0
  · subst i
    simpa using hzero
  · have h := congrArg (fun k : ℕ => (k : Fin n)) (hsum i hi)
    simp only [Nat.cast_add, Fin.cast_val_eq_self] at h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [add_comm] using h

/-- Odd-case matching criterion in circular coordinates after choosing the fixed-point cut. -/
theorem sole_fixed_circular_reflection (p : State (n+1))
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hfixed : ∀ i : Fin (n+1), p i=i → i=0)
    (hunique : ∀ a b : Fin (n+1), a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i, p i= -i :=
  circular_reflection_of_endpoint_sum p hzero
    (sole_zero_fixed_matching_reflection p hinv hnc hzero hfixed hunique)

/-- Even-case matching criterion in circular coordinates after choosing a fixed-point cut. -/
theorem two_fixed_circular_reflection [NeZero n] (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i, p i= -i :=
  circular_reflection_of_endpoint_sum p ((hfixed 0).mpr (Or.inl rfl))
    (two_fixed_matching_reflection p hinv hnc t ht hfixed hnoadj)

#print axioms sole_fixed_circular_reflection
#print axioms two_fixed_circular_reflection
end LRX.FiniteCuts
