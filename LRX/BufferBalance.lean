import LRX.BufferEndpoints

/-! The total contracted displacement vanishes for every balanced finite phase-zero
lift. Consequently a program reaching all target logical coordinates closes its
integer cursor automatically, including the winding of all nested calls. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem contracted_sum {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d) :
    (∑ i : Fin n, PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i)) =
      ∑ i : Fin n, PeriodicBuffer.contract (n : ℤ) (i : ℤ) := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hrem (i : Fin n) : ((i : ℤ)+d i)%(n : ℤ) = (p.symm i : ℤ) := by
    simpa only [add_zero, AffineLift.fin_mod] using (hd.2 i).eq
  have hsrem : (∑ i : Fin n, ((i : ℤ)+d i)%(n : ℤ)) = ∑ i : Fin n, (i : ℤ) := by
    simp_rw [hrem]
    exact Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
  have hspos : (∑ i : Fin n, ((i : ℤ)+d i)) = ∑ i : Fin n, (i : ℤ) := by
    rw [Finset.sum_add_distrib, hd.1, add_zero]
  have hdiv : (n : ℤ)*(∑ i : Fin n, ((i : ℤ)+d i)/(n : ℤ)) +
      (∑ i : Fin n, ((i : ℤ)+d i)%(n : ℤ)) = ∑ i : Fin n, ((i : ℤ)+d i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Int.mul_ediv_add_emod _ _)
  rw [hsrem, hspos] at hdiv
  have hq : (∑ i : Fin n, ((i : ℤ)+d i)/(n : ℤ))=0 := by
    have hz : (n : ℤ)*(∑ i : Fin n, ((i : ℤ)+d i)/(n : ℤ))=0 := by omega
    exact (mul_eq_zero.mp hz).resolve_left hn0
  have hpoint (i : Fin n) : PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) =
      PeriodicBuffer.contract (n : ℤ) (p.symm i : ℤ) + (((i : ℤ)+d i)/(n : ℤ))*((n : ℤ)-1) := by
    have hx : (i : ℤ)+d i = (p.symm i : ℤ) + (((i : ℤ)+d i)/(n : ℤ))*(n : ℤ) := by
      have hh := Int.emod_add_ediv_mul ((i : ℤ)+d i) (n : ℤ)
      rw [hrem i] at hh
      exact hh.symm
    conv_lhs => rw [hx]
    exact PeriodicBuffer.contract_period hn0 _ _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq, zero_mul, add_zero]
  exact Equiv.sum_comp p.symm (fun i : Fin n => PeriodicBuffer.contract (n : ℤ) (i : ℤ))

theorem closed_head_of_complete_coordinates (cs : List (Command n))
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (hy : ∀ i, (logicalRun cs initialLogical).coord i =
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i)) :
    (logicalRun cs initialLogical).head=0 := by
  have h := head_ledger cs (initialLogical (n := n))
  simp_rw [hy] at h
  rw [contracted_sum hd] at h
  simpa only [initialLogical, sub_zero, sub_self] using h

/-- The cursor-closing hypothesis is derived from completeness and balance. -/
theorem completed_service_endpoint (hn : 2 ≤ n) (cs : List (Command n))
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (hv : Valid cs initialLogical)
    (hy : ∀ i, (logicalRun cs initialLogical).coord i =
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i))
    (hb : (((logicalRun cs initialLogical).buffer : ℤ)+
      d (logicalRun cs initialLogical).buffer)%(n : ℤ)=0) :
    eval (compile cs) = p :=
  compiled_endpoint hn cs hd hv (closed_head_of_complete_coordinates cs hd hy) hy hb

#print axioms contracted_sum
#print axioms closed_head_of_complete_coordinates
#print axioms completed_service_endpoint
end LRX.BufferProgram
