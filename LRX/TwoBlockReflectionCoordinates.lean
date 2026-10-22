import LRX.ShortLiftUniqueness

namespace LRX.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Reflection about m-1 reverses the two consecutive blocks of lengths m and n-m. -/
theorem two_block_reflection_values (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) (i : Fin n) :
    (p.symm i).val=if i.val<n/2 then n/2-1-i.val else n+n/2-1-i.val := by
  have hm : 0<n/2 := by omega
  have hc : n/2-1<n := by omega
  have hv : (((n/2-1 : ℕ) : Fin n)).val=n/2-1 := by
    simp [Fin.val_natCast, Nat.mod_eq_of_lt hc]
  rw [hp]
  by_cases hi : i.val<n/2
  · have hle : i ≤ ((n/2-1 : ℕ) : Fin n) := by change i.val ≤ _; rw [hv]; omega
    rw [Fin.sub_val_of_le hle,hv,if_pos hi]
  · have hlt : ((n/2-1 : ℕ) : Fin n) < i := by change _ < i.val; rw [hv]; omega
    rw [Fin.coe_sub_iff_lt.mpr hlt,hv,if_neg hi]
    omega

theorem two_block_reflection_preserves_side (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) (i : Fin n) :
    (p.symm i).val<n/2 ↔ i.val<n/2 := by
  rw [two_block_reflection_values hn p hp i]
  have hi := i.isLt
  split_ifs <;> omega

theorem two_block_reflection_short (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) :
    ∀ i, 2*|displacement p.symm i| < (n : ℤ) := by
  intro i
  have hside := two_block_reflection_preserves_side hn p hp i
  have hi := i.isLt
  have hpi := (p.symm i).isLt
  have hab : |displacement p.symm i| ≤ (n : ℤ)-(n/2 : ℕ)-1 := by
    unfold displacement
    rw [abs_le]
    by_cases hl : i.val<n/2
    · have hp' := hside.mpr hl
      constructor <;> omega
    · have hp' : ¬(p.symm i).val<n/2 := fun h => hl (hside.mp h)
      constructor <;> omega
  omega

/-- The actual strictly short phase-zero lift of the block reflection is canonical. -/
theorem two_block_reflection_lift_canonical (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) :
    d=displacement p.symm := by
  apply strict_short_lift_unique hd
    (by simpa only [Equiv.symm_symm] using canonical_lift p.symm) hshort
  exact two_block_reflection_short hn p hp

#print axioms two_block_reflection_values
#print axioms two_block_reflection_lift_canonical
end LRX.FiniteCuts
