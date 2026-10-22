import LRX.FullCycleService
import LRX.NestedService

/-! Integer winding identities for any invariant set of labels, including an
entire recursive subtree. Balance of each separate cycle is not assumed. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def liftQuotient (d : Fin n → ℤ) (i : Fin n) : ℤ := ((i : ℤ)+d i)/(n : ℤ)

omit [NeZero n] in
theorem lift_endpoint_decomposition {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i : Fin n) :
    (i : ℤ)+d i=(p.symm i : ℤ)+(n : ℤ)*liftQuotient d i := by
  have hr : ((i : ℤ)+d i)%(n : ℤ)=(p.symm i : ℤ) := by
    simpa only [add_zero, AffineLift.fin_mod] using (hd.2 i).eq
  have h := Int.mul_ediv_add_emod ((i : ℤ)+d i) (n : ℤ)
  rw [hr] at h
  dsimp [liftQuotient]
  omega

theorem contracted_endpoint_decomposition {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i : Fin n) :
    PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) =
      PeriodicBuffer.contract (n : ℤ) (p.symm i : ℤ)+
        BufferMachine.slots n*liftQuotient d i := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [lift_endpoint_decomposition hd i, mul_comm (n : ℤ), PeriodicBuffer.contract_period hn]
  simp only [BufferMachine.slots]
  ring

omit [NeZero n] in
theorem sum_invariant_set (p : State n) (S : Finset (Fin n))
    (hS : S.image p.symm=S) (f : Fin n → ℤ) :
    (∑ i ∈ S, f (p.symm i))=∑ i ∈ S, f i := by
  have h := Finset.sum_image (f := f) (s := S) p.symm.injective.injOn
  rw [hS] at h
  exact h.symm

omit [NeZero n] in
/-- The winding of a union of cycles is the sum of endpoint quotient changes. -/
theorem cycle_displacement_sum {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (S : Finset (Fin n))
    (hS : S.image p.symm=S) :
    (∑ i ∈ S, d i)=(n : ℤ)*∑ i ∈ S, liftQuotient d i := by
  have he : ∀ i, d i=(p.symm i : ℤ)-(i : ℤ)+(n : ℤ)*liftQuotient d i := by
    intro i
    have h := lift_endpoint_decomposition hd i
    omega
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_invariant_set p S hS (fun i => (i : ℤ)), sub_self, zero_add, Finset.mul_sum]

/-- This is the head-shift formula for the whole serviced subtree. It applies
even when individual cycles have nonzero and mutually cancelling windings. -/
theorem cycle_logical_sum {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (S : Finset (Fin n))
    (hS : S.image p.symm=S) :
    (∑ i ∈ S, logicalDelta d i)=BufferMachine.slots n*∑ i ∈ S, liftQuotient d i := by
  simp only [logicalDelta, contracted_endpoint_decomposition hd]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_invariant_set p S hS (fun i => PeriodicBuffer.contract (n : ℤ) (i : ℤ)),
    ← Finset.mul_sum]
  omega

/-- Delivering exactly an invariant set shifts the head by the winding of that
whole set. No zero-winding assumption is imposed on its component cycles. -/
theorem subtree_head_winding {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (S : Finset (Fin n))
    (hS : S.image p.symm=S) (cs : List (Command n)) (s : Logical n)
    (he : ∀ i, (logicalRun cs s).coord i=s.coord i+
      if i ∈ S then logicalDelta d i else 0) :
    (logicalRun cs s).head-s.head=BufferMachine.slots n*∑ i ∈ S, liftQuotient d i := by
  have h := head_ledger cs s
  simp_rw [he] at h
  rw [Finset.sum_add_distrib] at h
  have hs : (∑ i : Fin n, if i ∈ S then logicalDelta d i else 0)=
      ∑ i ∈ S, logicalDelta d i := by simp
  rw [hs, cycle_logical_sum hd S hS] at h
  omega

theorem lifted_subtree_frame {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (S active : Finset (Fin n))
    (hS : S.image p.symm=S) (cs : List (Command n)) (s : Logical n)
    (he : ∀ i, (logicalRun cs s).coord i=s.coord i+
      if i ∈ S then logicalDelta d i else 0)
    (hb : (logicalRun cs s).buffer=s.buffer)
    (ha : Disjoint active S) : FrameEquivalent active s (logicalRun cs s) := by
  refine ⟨hb.symm, ?_, ?_⟩
  · apply Int.modEq_iff_dvd.mpr
    rw [subtree_head_winding hd S hS cs s he]
    exact dvd_mul_right _ _
  · intro i hi
    have hn : i ∉ S := Finset.disjoint_left.mp ha hi
    rw [he i, ite_eq_right hn, add_zero]

#print axioms cycle_displacement_sum
#print axioms cycle_logical_sum
#print axioms subtree_head_winding
#print axioms lifted_subtree_frame
end LRX.BufferProgram
