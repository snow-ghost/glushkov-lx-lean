import LRX.WindowSelectedEnergy

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ}

def familyPositions : List (FillingWindow n) → Finset (Fin n)
  | [] => ∅
  | A :: As => windowPositions A.window ∪ familyPositions As

@[simp] theorem mem_family_positions (As : List (FillingWindow n)) (i : Fin n) :
    i ∈ familyPositions As ↔ ∃ A ∈ As, Contains A.window i := by
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih => simp [familyPositions,windowPositions,ih,or_and_right,exists_or]

/-- Exact selected size and balance, and the aggregate fixed-position energy
bound, for the actual original fillings of disjoint physical windows. -/
theorem window_family_selected_energy (As : List (FillingWindow n)) (p : State n)
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart) :
    (familyPositions As).card = (As.map (fun A => A.size)).sum ∧
    (∑ i ∈ familyPositions As, displacement p i) = 0 ∧
    2*(∑ i ∈ familyPositions As, |displacement p i|)+
      ((familyPositions As \ p.support).card : ℤ) ≤
      (As.map (fun A => (A.size : ℤ)^2)).sum := by
  classical
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hmA := hm A (List.mem_cons_self ..)
    have hmAs := fun B hB => hm B (List.mem_cons_of_mem _ hB)
    obtain ⟨hcard,hbalance,henergy⟩ := ih hmAs hAs
    have hdis : Disjoint (windowPositions A.window) (familyPositions As) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨B,hB,hBi⟩ := (mem_family_positions As i).mp hj
      exact hA B hB i (Finset.mem_filter.mp hi).2 hBi
    have hdisFixed : Disjoint (windowPositions A.window \ p.support) (familyPositions As \ p.support) :=
      hdis.mono Finset.sdiff_subset Finset.sdiff_subset
    have hbA := matching_window_balance A.window p A.filling hmA
    have heA := matching_window_energy_fixed A.window p A.filling hmA
    refine ⟨?_,?_,?_⟩
    · simp only [familyPositions,Finset.card_union_of_disjoint hdis,window_positions_card,hcard,List.map_cons,List.sum_cons]
    · rw [familyPositions,Finset.sum_union hdis,hbA,hbalance,add_zero]
    · simp only [familyPositions,Finset.sum_union hdis,Finset.union_sdiff_distrib,
        Finset.card_union_of_disjoint hdisFixed,Nat.cast_add,List.map_cons,List.sum_cons]
      linarith

#print axioms window_family_selected_energy
end LRX.FiniteWindow
