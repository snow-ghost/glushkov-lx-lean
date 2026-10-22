import LRX.BufferFrame

/-! A certified resumption rule for a nested call. The head shift is computed
from the coordinate permutation and all integer winding contributions of the
completed call. It is not identified with the root cycle winding alone. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

theorem service_head_winding (cs : List (Command n)) (s : Logical n)
    (perm : Equiv.Perm (Fin n)) (winding : Fin n → ℤ)
    (he : ∀ i, (logicalRun cs s).coord i =
      s.coord (perm i)+BufferMachine.slots n*winding i) :
    (logicalRun cs s).head-s.head=BufferMachine.slots n*∑ i, winding i := by
  have h := head_ledger cs s
  simp_rw [he] at h
  rw [Finset.sum_add_distrib, Equiv.sum_comp perm s.coord, ← Finset.mul_sum] at h
  omega

theorem frame_after_service (active : Finset (Fin n)) (cs : List (Command n))
    (s : Logical n) (perm : Equiv.Perm (Fin n)) (winding : Fin n → ℤ)
    (he : ∀ i, (logicalRun cs s).coord i =
      s.coord (perm i)+BufferMachine.slots n*winding i)
    (hb : (logicalRun cs s).buffer=s.buffer)
    (hfixed : ∀ i ∈ active, perm i=i ∧ winding i=0) :
    FrameEquivalent active s (logicalRun cs s) := by
  refine ⟨hb.symm, ?_, ?_⟩
  · apply Int.modEq_iff_dvd.mpr
    rw [service_head_winding cs s perm winding he]
    exact dvd_mul_right _ _
  · intro i hi
    rw [he i, (hfixed i hi).1, (hfixed i hi).2, mul_zero, add_zero]

/-- A completed child can be inserted before a parent continuation provided it
returns the buffer and fixes protected labels. All child winding is included. -/
theorem resume_after_service (active : Finset (Fin n))
    (child parent : List (Command n)) (s : Logical n)
    (perm : Equiv.Perm (Fin n)) (winding : Fin n → ℤ)
    (he : ∀ i, (logicalRun child s).coord i =
      s.coord (perm i)+BufferMachine.slots n*winding i)
    (hb : (logicalRun child s).buffer=s.buffer)
    (hfixed : ∀ i ∈ active, perm i=i ∧ winding i=0)
    (hstart : s.buffer ∈ active)
    (huses : ∀ c ∈ parent, Uses active c)
    (hc : Valid child s) (hp : Valid parent s) :
    Valid (child++parent) s ∧
      FrameEquivalent active (logicalRun parent s) (logicalRun (child++parent) s) := by
  have hf := frame_after_service active child s perm winding he hb hfixed
  refine ⟨(valid_append child parent s).mpr ⟨hc, valid_frame hf hstart parent huses hp⟩, ?_⟩
  rw [logicalRun_append]
  exact (run_frame hf hstart parent huses).1

/-- Logical resumption compiles to a real lifted execution whenever the entry
configuration represents the suspended service state. -/
theorem nested_execution [NeZero n] (hn : 2 ≤ n)
    (active : Finset (Fin n)) (child parent : List (Command n))
    {physical : LiftedModel.Configuration n} {s : Logical n}
    (hm : Matches physical s)
    (perm : Equiv.Perm (Fin n)) (winding : Fin n → ℤ)
    (he : ∀ i, (logicalRun child s).coord i =
      s.coord (perm i)+BufferMachine.slots n*winding i)
    (hb : (logicalRun child s).buffer=s.buffer)
    (hfixed : ∀ i ∈ active, perm i=i ∧ winding i=0)
    (hstart : s.buffer ∈ active) (huses : ∀ c ∈ parent, Uses active c)
    (hc : Valid child s) (hp : Valid parent s) :
    Matches (LiftedModel.run (compile (child++parent)) physical)
      (logicalRun (child++parent) s) := by
  exact compile_correct hn _ hm
    (resume_after_service active child parent s perm winding he hb hfixed hstart huses hc hp).1

#print axioms service_head_winding
#print axioms resume_after_service
#print axioms nested_execution
end LRX.BufferProgram
