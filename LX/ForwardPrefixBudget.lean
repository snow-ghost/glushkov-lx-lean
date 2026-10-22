import LX.FinitePrefixRotation

namespace LX.FiniteDropBudget
open scoped BigOperators
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The initial ascending chain is charged directly to the finite drop
budget; no hypothesis on shallow cycles is required. -/
theorem forward_prefix_drop_bound (p : LRX.State n) (r : ℕ)
    (hr0 : 0 < r) (hr : r ≤ n) (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0)
    (hd : 2 ≤ (descendingPositions p).card) :
    3*((descendingPositions p).card : ℤ) ≤ (n : ℤ)-(r : ℤ)+
      (∑ i, |displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card := by
  obtain ⟨q,hqfix,hqpre,hqhead,hqd,hqu,hqcost⟩ := contract_forward_prefix p r hr0 hp hhead
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    have hqlast : q 0 ≠ Fin.last k := by
      intro he
      have hsub : descendingPositions q ⊆ {Fin.last k} := by
        intro i hi
        have hid := (mem_descendingPositions q i).mp hi
        by_cases hilast : i=Fin.last k
        · exact Finset.mem_singleton.mpr hilast
        have hil : i.val < k := by
          have := i.isLt
          have hn : i.val ≠ k := fun h => hilast (Fin.ext h)
          omega
        have hi0 : 0 < i.val := by omega
        have hfix := (hqpre 0 (by simpa using hr0)).2 i
          (by simpa using hi0) (by simpa only [he,Fin.val_last] using hil)
        rw [hfix] at hid
        omega
      have hc := Finset.card_le_card hsub
      rw [hqd,Finset.card_singleton] at hc
      omega
    have hq := fixed_middle_drop_bound q r hr hqhead hqlast hqfix
    rw [hqd,hqu] at hq
    omega

#print axioms forward_prefix_drop_bound
end LX.FiniteDropBudget
