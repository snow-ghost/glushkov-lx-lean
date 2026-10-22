import LRX.PortLoadMass

/-! Every cut of a balanced permutation lift has zero net signed flow.
Consequently its actual load is even, and a positive load is at least two. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem remainder_sum_equiv (a : Fin n → ℤ) (e : Fin n ≃ Fin n)
    (ha : ∀ i, (a i : Fin n)=e i) :
    (∑ i : Fin n, a i%(n : ℤ))=∑ i : Fin n, (i : ℤ) := by
  have hp (i : Fin n) : a i%(n : ℤ)=(e i : ℤ) := by
    rw [← AffineLift.residue_val]
    exact congrArg (fun j : Fin n => (j : ℤ)) (ha i)
  simp_rw [hp]
  exact Equiv.sum_comp e (fun j : Fin n => (j : ℤ))

theorem cut_signed_balance {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (r : ℤ) :
    (∑ i : Fin n, signedCrossing (n := n) (i : ℤ) (d i) r)=0 := by
  have hrem1 : (∑ i : Fin n, (r-(i : ℤ)-d i)%(n : ℤ))=∑ i : Fin n, (i : ℤ) := by
    apply remainder_sum_equiv _ (p.symm.trans (Equiv.subLeft ((r-c : ℤ) : Fin n)))
    intro i
    change ((r-(i : ℤ)-d i : ℤ) : Fin n)=((r-c : ℤ) : Fin n)-p.symm i
    simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self]
    have h := AffineLift.lift_residue hd i
    linear_combination -h
  have hrem0 : (∑ i : Fin n, (r-(i : ℤ))%(n : ℤ))=∑ i : Fin n, (i : ℤ) := by
    apply remainder_sum_equiv _ (Equiv.subLeft (r : Fin n))
    intro i
    simp [Int.cast_sub]
  have hsum : (∑ i : Fin n, (r-(i : ℤ)-d i))=(∑ i : Fin n, (r-(i : ℤ))) := by
    rw [Finset.sum_sub_distrib, hd.1, sub_zero]
  have hdiv (a : Fin n → ℤ) :
      (n : ℤ)*(∑ i, a i/(n : ℤ))+(∑ i, a i%(n : ℤ))=∑ i, a i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Int.mul_ediv_add_emod _ _)
  have h1 := hdiv (fun i => r-(i : ℤ)-d i)
  have h0 := hdiv (fun i => r-(i : ℤ))
  rw [hrem1, hsum] at h1
  rw [hrem0] at h0
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hq : (∑ i : Fin n, (r-(i : ℤ)-d i)/(n : ℤ))=
      ∑ i : Fin n, (r-(i : ℤ))/(n : ℤ) := by
    apply mul_left_cancel₀ hn
    omega
  simp only [signedCrossing, Finset.sum_sub_distrib, hq, sub_self]

theorem port_load_twice_positive {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (r : Fin n) :
    portLoad d r=2*∑ i : Fin n, max (signedCrossing (n := n) (i : ℤ) (d i) (r : ℤ)) 0 := by
  have habs (x : ℤ) : |x|=2*max x 0-x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]; ring
    · rw [abs_of_nonpos (by omega : x ≤ 0), max_eq_right (by omega : x ≤ 0)]; ring
  rw [port_load_original]
  simp_rw [edge_signed_crossing, habs]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, cut_signed_balance hd, sub_zero]

theorem positive_port_load_ge_two {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (r : Fin n) (hpos : 0 < portLoad d r) :
    2 ≤ portLoad d r := by
  rw [port_load_twice_positive hd r] at hpos ⊢
  omega

#print axioms cut_signed_balance
#print axioms port_load_twice_positive
#print axioms positive_port_load_ge_two
end LRX.RotationWords
