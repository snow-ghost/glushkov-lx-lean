import LRX.PacketCoreBalance
import LRX.ZeroGapRootCoverCount
import Mathlib

/-! Cycle representatives and fixed points give a root cover of the sorting
event graph; all cycles inside the packet can share one root. -/
namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def cycleRoot (q : State n) : Fin n := by
  classical
  exact if h : q.support.Nonempty then q.support.min' h else 0

theorem cycle_root_mem {q : State n} (hq : q.IsCycle) : cycleRoot q ∈ q.support := by
  classical
  have hne := hq.nonempty_support
  simp only [cycleRoot,dif_pos hne]
  exact Finset.min'_mem _ _

theorem cycle_root_same_cycle {g q : State n} (hq : q ∈ g.cycleFactorsFinset)
    {i : Fin n} (hi : i ∈ q.support) : g.SameCycle (cycleRoot q) i := by
  classical
  have hroot : cycleRoot q ∈ q.support := cycle_root_mem (q := q) (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
  have he : q=g.cycleOf i := Equiv.Perm.cycle_is_cycleOf (f := g) (c := q) hi hq
  have hroot' : cycleRoot q ∈ (g.cycleOf i).support := by rw [← he]; exact hroot
  exact ((Equiv.Perm.mem_support_cycleOf_iff (f := g) (x := i) (y := cycleRoot q)).mp hroot').1.symm

noncomputable def cycleRoots (p : State n) : List (Fin n) := by
  classical
  exact (p⁻¹).supportᶜ.toList ++ (p⁻¹).cycleFactorsFinset.toList.map cycleRoot

theorem cycle_roots_cover {p : State n} {events : List (Event n)}
    (hprod : (events.map eventSwap).prod=p) :
    ∀ i : Fin n, ∃ r ∈ cycleRoots p, EventReaches events r i := by
  classical
  intro i
  by_cases hi : i ∈ (p⁻¹).support
  · obtain ⟨q,hq,hiq⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hi
    refine ⟨cycleRoot q,?_,cycle_event_reachable events p hprod (cycle_root_same_cycle hq hiq)⟩
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨q,by simpa using hq,rfl⟩
  · exact ⟨i,List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_compl.mpr hi)),Relation.ReflTransGen.refl⟩

theorem cycle_root_count {p : State n} {events : List (Event n)}
    (hprod : (events.map eventSwap).prod=p) :
    p.support.card ≤ events.length+(p⁻¹).cycleFactorsFinset.card := by
  classical
  have h := root_cover_count events (cycleRoots p) (cycle_roots_cover hprod)
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  simp only [cycleRoots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin,Equiv.Perm.support_inv] at h
  omega

noncomputable def outsideCycles (p : State n) (d : Fin n → ℤ) (root : Fin n) : Finset (State n) := by
  classical
  exact (p⁻¹).cycleFactorsFinset.filter (fun q => ¬q.support ⊆ PrunedLift.core p d root)

noncomputable def packetCycleRoots (p : State n) (d : Fin n → ℤ) (root : Fin n) : List (Fin n) := by
  classical
  exact root :: ((p⁻¹).supportᶜ.toList ++ (outsideCycles p d root).toList.map cycleRoot)


#print axioms cycle_root_count
end LRX.ZeroGap
