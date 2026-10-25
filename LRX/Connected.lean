import LRX.Graph
import Mathlib

namespace LRX

/-- Reachability from one in a Cayley graph forms a subgroup. -/
def reachableSubgroup {G : Type*} [Group G] (S : Set G) : Subgroup G where
  carrier := {p | (SimpleGraph.mulCayley S).Reachable 1 p}
  one_mem' := .rfl
  mul_mem' := by
    intro a b ha hb
    have ht := hb.map (leftTranslate S a)
    change (SimpleGraph.mulCayley S).Reachable (a * 1) (a * b) at ht
    simp only [mul_one] at ht
    exact ha.trans ht
  inv_mem' := by
    intro a ha
    change (SimpleGraph.mulCayley S).Reachable 1 a⁻¹
    have ht := ha.symm.map (leftTranslate S a⁻¹)
    change (SimpleGraph.mulCayley S).Reachable (a⁻¹ * a) (a⁻¹ * 1) at ht
    simpa only [inv_mul_cancel, mul_one] using ht

theorem connected_of_generates {G : Type*} [Group G] (S : Set G)
    (hgen : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  have hsub : Subgroup.closure S ≤ reachableSubgroup S := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change (SimpleGraph.mulCayley S).Reachable 1 g
    by_cases h : 1 = g
    · rw [← h]
    · exact ((SimpleGraph.mulCayley_adj' S 1 g).mpr
        ⟨h, g, hg, Or.inl (one_mul g)⟩).reachable
  rw [hgen] at hsub
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  exact ⟨1, fun g => hsub (Subgroup.mem_top g)⟩

theorem generators_closure (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Subgroup.closure (generators n) = ⊤ := by
  have hrot : L n (0 : Fin n) = 1 := by
    cases n with
    | zero => omega
    | succ k => exact finRotate_apply_zero
  have hgen := Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate_of_le hn)
    (support_finRotate_of_le hn) (0 : Fin n)
  change Subgroup.closure ({L n, Equiv.swap 0 (L n 0)} : Set (State n)) = ⊤ at hgen
  rw [hrot] at hgen
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp [generators, X]

theorem connected (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (graph n).Connected :=
  connected_of_generates _ (generators_closure n hn)


end LRX
