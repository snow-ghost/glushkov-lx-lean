import LRX.BufferMotion

/-! Initial and final contracts for the periodic buffer compiler. Reconstruction
is over integers, so a closed physical service cannot silently discard winding. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open BufferMachine
variable {n : ℕ} [NeZero n]

def initialLogical : Logical n :=
  ⟨0, fun i => PeriodicBuffer.contract (n : ℤ) (i : ℤ), 0⟩

theorem initial_matches (hn : 2 ≤ n) :
    Matches (LiftedModel.initial (n := n)) initialLogical := by
  refine ⟨rfl, LiftedModel.initial_aligned, ?_, ?_⟩
  · simp [initialLogical, LiftedModel.initial, PeriodicBuffer.contract]
  · intro i
    change (i : ℤ) = if i=0 then
      PeriodicBuffer.buffer (slots n) 0 (PeriodicBuffer.contract (n : ℤ) (i : ℤ))
      else PeriodicBuffer.passive (slots n) 0 (PeriodicBuffer.contract (n : ℤ) (i : ℤ))
    by_cases hi : i=0
    · subst i; simp [PeriodicBuffer.contract, PeriodicBuffer.buffer]
    · rw [ite_eq_right hi]
      have hz : (i : ℤ)%(slots n+1) ≠ 0 := by
        rw [show slots n+1=(n : ℤ) by ring, AffineLift.fin_mod]
        intro he
        apply hi
        exact_mod_cast he
      simpa only [slots, sub_add_cancel] using
        (PeriodicBuffer.reconstruct_passive (slots_pos hn) (i : ℤ) hz).symm

omit [NeZero n] in
theorem endpoint_residue_injective {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {i j : Fin n}
    (h : ((i : ℤ)+d i)%(n : ℤ) = ((j : ℤ)+d j)%(n : ℤ)) : i=j := by
  have hi := (hd.2 i).eq
  have hj := (hd.2 j).eq
  simp only [add_zero, AffineLift.fin_mod] at hi hj
  rw [hi, hj] at h
  apply p.symm.injective
  apply Fin.ext
  exact_mod_cast h

/-- A legal buffer program with contracted target coordinates and the right final
buffer realizes the original exact integer displacements, not only their residues. -/
theorem compiled_exact_positions (hn : 2 ≤ n) (cs : List (Command n))
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (hv : Valid cs initialLogical)
    (hhead : (logicalRun cs initialLogical).head=0)
    (hy : ∀ i, (logicalRun cs initialLogical).coord i =
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i))
    (hb : (((logicalRun cs initialLogical).buffer : ℤ)+
      d (logicalRun cs initialLogical).buffer)%(n : ℤ)=0) :
    ∀ i, (LiftedModel.run (compile cs) (LiftedModel.initial (n := n))).position i = (i : ℤ)+d i := by
  have hm := compile_correct hn cs (initial_matches hn) hv
  intro i
  rw [hm.2.positions i, hm.1, hhead, hy i]
  split_ifs with hi
  · have hz : ((i : ℤ)+d i)%(slots n+1)=0 := by
      simpa only [slots, sub_add_cancel, hi] using hb
    simpa only [slots, sub_add_cancel] using
      PeriodicBuffer.reconstruct_buffer (slots_pos hn) ((i : ℤ)+d i) hz
  · have hz : ((i : ℤ)+d i)%(slots n+1)≠0 := by
      intro hzero
      have he : ((i : ℤ)+d i)%(n : ℤ) =
          (((logicalRun cs initialLogical).buffer : ℤ)+d (logicalRun cs initialLogical).buffer)%(n : ℤ) := by
        simpa only [slots, sub_add_cancel, hb] using hzero
      exact hi (endpoint_residue_injective hd he)
    simpa only [slots, sub_add_cancel] using
      PeriodicBuffer.reconstruct_passive (slots_pos hn) ((i : ℤ)+d i) hz

theorem compiled_endpoint (hn : 2 ≤ n) (cs : List (Command n))
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (hv : Valid cs initialLogical)
    (hhead : (logicalRun cs initialLogical).head=0)
    (hy : ∀ i, (logicalRun cs initialLogical).coord i =
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i))
    (hb : (((logicalRun cs initialLogical).buffer : ℤ)+
      d (logicalRun cs initialLogical).buffer)%(n : ℤ)=0) : eval (compile cs) = p := by
  have hm := compile_correct hn cs (initial_matches hn) hv
  have hc : (LiftedModel.run (compile cs) (LiftedModel.initial (n := n))).cursor=0 := hm.1.trans hhead
  exact LiftedModel.eval_of_exact_positions hn (compile cs) (hc ▸ hd)
    (compiled_exact_positions hn cs hd hv hhead hy hb)

#print axioms initial_matches
#print axioms compiled_exact_positions
#print axioms compiled_endpoint
end LRX.BufferProgram
