import LX.ExtremeEventBranch
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem singleton_component_product_fixed (events : List (Event n)) (b : Fin n)
    (hb : (eventComponent events b).card=1) : (events.map eventSwap).prod b=b := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hb
  have hroot : b ∈ eventComponent events b := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  have hprod : (events.map eventSwap).prod b ∈ eventComponent events b :=
    (mem_eventComponent _ _ _).mpr (event_product_reaches events events (fun _ h => h) b)
  rw [hi,Finset.mem_singleton] at hroot hprod
  exact hprod.trans hroot.symm

/-- Inserting a neighbor of an extreme cannot break an adjacency whose
ends both avoid that extreme. -/
theorem rank_adjacent_after_extreme_insertion (T : Finset (Fin n)) (a b : Fin n)
    (hext : IsExtreme (insert b T) a) (hgap : RankAdjacent (insert b T) a b)
    {x y : Fin n} (hxy : RankAdjacent T x y) (hxa : x ≠ a) (hya : y ≠ a) :
    RankAdjacent (insert b T) x y := by
  classical
  refine ⟨Finset.mem_insert_of_mem hxy.1,Finset.mem_insert_of_mem hxy.2.1,hxy.2.2.1,?_⟩
  intro z hz hbetween
  rcases Finset.mem_insert.mp hz with hzb | hz
  · subst z
    have hx : x ∈ insert b T := Finset.mem_insert_of_mem hxy.1
    have hy : y ∈ insert b T := Finset.mem_insert_of_mem hxy.2.1
    have hgx := hgap.2.2.2 x hx
    have hgy := hgap.2.2.2 y hy
    have hnx : x.val ≠ a.val := fun h => hxa (Fin.ext h)
    have hny : y.val ≠ a.val := fun h => hya (Fin.ext h)
    rcases hext with h | h
    · have := h x hx; have := h y hy; omega
    · have := h x hx; have := h y hy; omega
  · exact hxy.2.2.2 z hz hbetween

theorem remaining_pair_adjacent (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hext : IsExtreme ({a,b,c} : Finset (Fin n)) a) :
    RankAdjacent ({a,b,c} : Finset (Fin n)) c b := by
  classical
  refine ⟨by simp,by simp,Ne.symm hbc,?_⟩
  intro z hz hz'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · rcases hext with h | h
    · have := h b (by simp); have := h c (by simp); omega
    · have := h b (by simp); have := h c (by simp); omega
  · omega
  · omega

#print axioms rank_adjacent_after_extreme_insertion
end LX.Core.ZeroGap
