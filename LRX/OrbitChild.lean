import LRX.ChildService
import LRX.CycleOrbit

/-! A canonical paid child call for one cycle of an arbitrary target permutation.
Individual cycle winding may be nonzero. The input parent is outside this cycle. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def orbitChild (p : State n) (d : Fin n → ℤ) (a parent : Fin n) : List (Command n) :=
  [.exchange a] ++ itinerary (logicalDelta d) ((p⁻¹).toList a) ++ [.exchange parent]

theorem orbit_child_correct [NeZero n] {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : (p⁻¹) a ≠ a) (t : Logical n)
    (hout : t.buffer ∉ orbitLabels p a)
    (hcoords : ∀ i ∈ orbitLabels p a, t.coord i=PeriodicBuffer.contract (n : ℤ) (i : ℤ))
    (hh : HeadReady t) (hentry : (t.coord a-t.head)%BufferMachine.slots n=0) :
    let cs := orbitChild p d a t.buffer
    Valid cs t ∧
    (logicalRun cs t).buffer=t.buffer ∧
    (∀ i, (logicalRun cs t).coord i=t.coord i+
      if i ∈ orbitLabels p a then logicalDelta d i else 0) ∧
    (logicalRun cs t).head-t.head=BufferMachine.slots n*∑ i ∈ orbitLabels p a, liftQuotient d i ∧
    rotations (compile cs)=∑ i ∈ orbitLabels p a, (logicalDelta d i).natAbs := by
  dsimp only
  obtain ⟨rest, he, hnd, hset, hfollow⟩ := exists_orbit_itinerary p a ha
  have hword : orbitChild p d a t.buffer=childService (logicalDelta d) a rest t.buffer := by
    simp only [orbitChild, childService, he]
  rw [hword]
  have hmem (i : Fin n) : i ∈ a::rest ↔ i ∈ orbitLabels p a := by
    rw [← hset, List.mem_toFinset]
  have hs : BufferMachine.slots n ∣ ((a::rest).map (logicalDelta d)).sum := by
    rw [← List.sum_toFinset _ hnd, hset, cycle_logical_sum hd _ (orbitLabels_invariant p a)]
    exact dvd_mul_right _ _
  have hcoordinate (i : Fin n) := child_service_coordinates (logicalDelta d) a rest t hnd i
  simp only [hmem] at hcoordinate
  refine ⟨?_, child_service_buffer _ _ _ _, hcoordinate, ?_, ?_⟩
  · apply child_service_valid (initialLogical (n := n)).coord (logicalDelta d) a rest t hnd
    · simpa only [hmem] using hout
    · intro i hi
      exact hcoords i ((hmem i).mp hi)
    · exact hh
    · exact hentry
    · exact follows_compatible hd (a::rest) hfollow
    · exact hs
  · exact subtree_head_winding hd _ (orbitLabels_invariant p a) _ t hcoordinate
  · rw [child_service_rotations, ← List.sum_toFinset _ hnd, hset]

/-- This orbit constructor is a literal lifted execution from every matching
physical entry state, including entries with an already wound cursor. -/
theorem orbit_child_execution [NeZero n] (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : (p⁻¹) a ≠ a)
    {t : Logical n} {s : LiftedModel.Configuration n} (hm : Matches s t)
    (hout : t.buffer ∉ orbitLabels p a)
    (hcoords : ∀ i ∈ orbitLabels p a, t.coord i=PeriodicBuffer.contract (n : ℤ) (i : ℤ))
    (hentry : (t.coord a-t.head)%BufferMachine.slots n=0) :
    Matches (LiftedModel.run (compile (orbitChild p d a t.buffer)) s)
      (logicalRun (orbitChild p d a t.buffer) t) := by
  have hh : HeadReady t := by
    change (t.coord t.buffer-t.head)%BufferMachine.slots n=0
    rw [← hm.1]
    exact hm.2.head
  exact compile_correct hn _ hm (orbit_child_correct hd a ha t hout hcoords hh hentry).1

#print axioms orbit_child_correct
#print axioms orbit_child_execution
end LRX.BufferProgram
