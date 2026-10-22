import LRX.BufferMotion

/-! A concrete move-and-handoff constructor. Congruent contracted endpoints
suffice for handing the buffer to a specified named token. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def transfer (d : ℤ) (j : Fin n) : List (Command n) := move d ++ [.exchange j]

theorem run_transfer (d : ℤ) (j : Fin n) (t : Logical n) :
    logicalRun (transfer d j) t =
      ⟨j, Function.update t.coord t.buffer (t.coord t.buffer+d), t.head+d⟩ := by
  rw [transfer, logicalRun_append, run_move]
  rfl

theorem transfer_valid (d : ℤ) (j : Fin n) (t : Logical n)
    (hhead : (t.coord t.buffer-t.head)%BufferMachine.slots n=0)
    (hne : j ≠ t.buffer)
    (hgoal : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer+d) (t.coord j)) :
    Valid (transfer d j) t := by
  have hzero : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer-t.head) 0 := by
    simpa only [Int.ModEq, Int.zero_emod] using hhead
  have hbuf : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer) t.head := by
    simpa only [sub_add_cancel, zero_add] using hzero.add_right t.head
  have ht := (hgoal.symm.trans (hbuf.add_right d)).sub_right (t.head+d)
  have hc : (t.coord j-(t.head+d))%BufferMachine.slots n=0 := by
    simpa only [Int.ModEq, sub_self, Int.zero_emod] using ht
  apply (valid_append (move d) [.exchange j] t).mpr
  refine ⟨move_valid d t, ?_⟩
  rw [run_move]
  refine ⟨⟨hne, ?_⟩, True.intro⟩
  simpa only [shift, Function.update_of_ne hne] using hc

theorem transfer_correct [NeZero n] (hn : 2 ≤ n) (d : ℤ) (j : Fin n)
    {s : LiftedModel.Configuration n} {t : Logical n} (hm : Matches s t)
    (hne : j ≠ t.buffer)
    (hgoal : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer+d) (t.coord j)) :
    Matches (LiftedModel.run (compile (transfer d j)) s)
      ⟨j, Function.update t.coord t.buffer (t.coord t.buffer+d), t.head+d⟩ := by
  have hh : (t.coord t.buffer-t.head)%BufferMachine.slots n=0 := by
    rw [← hm.1]; exact hm.2.head
  have h := compile_correct hn (transfer d j) hm (transfer_valid d j t hh hne hgoal)
  simpa only [run_transfer] using h

theorem transfer_rotation_price (d : ℤ) (j : Fin n) :
    rotations (compile (transfer d j)) = d.natAbs := by
  rw [transfer, compile_append, rotations_append, move_rotation_price]
  simp [compile, rotations, word]

theorem transfer_length (d : ℤ) (j : Fin n) :
    (compile (transfer d j)).length = 2*d.natAbs+1 := by
  simp [transfer, compile_append, compile, move_length, word]

/-- Endpoint congruence of actual lifted arrows supplies the handoff condition. -/
theorem contracted_transfer_correct [NeZero n] (hn : 2 ≤ n) (j : Fin n)
    {s : LiftedModel.Configuration n} {t : Logical n} (hm : Matches s t)
    (hne : j ≠ t.buffer) (x target z : ℤ)
    (hstart : t.coord t.buffer = PeriodicBuffer.contract (n : ℤ) x)
    (hnext : t.coord j = PeriodicBuffer.contract (n : ℤ) z)
    (hend : Int.ModEq (n : ℤ) target z) :
    Matches (LiftedModel.run
      (compile (transfer (PeriodicBuffer.contract (n : ℤ) target-PeriodicBuffer.contract (n : ℤ) x) j)) s)
      ⟨j, Function.update t.coord t.buffer (PeriodicBuffer.contract (n : ℤ) target),
        t.head+(PeriodicBuffer.contract (n : ℤ) target-PeriodicBuffer.contract (n : ℤ) x)⟩ := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcalc : PeriodicBuffer.contract (n : ℤ) x +
      (PeriodicBuffer.contract (n : ℤ) target-PeriodicBuffer.contract (n : ℤ) x) =
      PeriodicBuffer.contract (n : ℤ) target := by ring
  have hg : Int.ModEq (BufferMachine.slots n)
      (t.coord t.buffer + (PeriodicBuffer.contract (n : ℤ) target-PeriodicBuffer.contract (n : ℤ) x))
      (t.coord j) := by
    rw [hstart, hnext, hcalc]
    exact PeriodicBuffer.contract_modEq hn0 hend
  have h := transfer_correct hn _ j hm hne hg
  simpa only [hstart, hcalc] using h

#print axioms transfer_correct
#print axioms transfer_rotation_price
#print axioms contracted_transfer_correct
end LRX.BufferProgram
