import LRX.ProtectedBlockOrder
import LRX.CutNeighborUnique
import LRX.ShallowTwoNeighbors

namespace LRX.ContractionBlocks.System
variable {m k : ℕ} {P : State (m+1)} {q : State (k+1)}

theorem extreme_pair_full_cases (x y : Fin (k+1))
    (he : ZeroGap.ExtremePair Finset.univ x y) :
    (x=0 ∧ y=Fin.last k) ∨ (x=Fin.last k ∧ y=0) := by
  have hzero := he.2.2.2 0 (Finset.mem_univ _)
  have hlast := he.2.2.2 (Fin.last k) (Finset.mem_univ _)
  have hx := x.isLt
  have hy := y.isLt
  simp only [Fin.val_zero,Fin.val_last] at hzero hlast
  have hv : (x.val=0 ∧ y.val=k) ∨ (x.val=k ∧ y.val=0) := by omega
  rcases hv with h | h
  · exact Or.inl ⟨Fin.ext h.1,Fin.ext h.2⟩
  · exact Or.inr ⟨Fin.ext h.1,Fin.ext h.2⟩

theorem protected_shallow_unit (B : System P q) (hp : q.IsCycle)
    (hs : FiniteCuts.Shallow q) (hfull : q.support=Finset.univ)
    (gap : Fin m) (hB : B.Protected gap.val) (hk : 0 < k)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (hwide : h < (k : ℤ)+(f gap.succ-f gap.castSucc-1)) :
    ∃ a : Fin (k+1), |FiniteCuts.displacement q a|=1 ∧
      ((B.lastLabel a).val ≤ gap.val ↔ (P (B.lastLabel a)).val ≤ gap.val) := by
  have hno := B.protected_no_extreme_arrows gap hB hk f hf h hshort hwide
  have hno' : ∀ x y, ZeroGap.ExtremePair q.support x y → q x ≠ y := by
    intro x y he
    rw [hfull] at he
    rcases extreme_pair_full_cases x y he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hno.1
    · exact hno.2
  obtain ⟨a,b,x,y,hab,habq,hxy,hxyq,hneq⟩ := ZeroGap.shallow_cycle_two_rank_neighbors hp hs hno'
  rw [hfull] at hab hxy
  have hu := FiniteCuts.full_carrier_neighbor_unit hab
  have hv := FiniteCuts.full_carrier_neighbor_unit hxy
  have hfirst : StrictMono (fun i : Fin (k+1) => (B.firstLabel i).val) := by
    intro i j hij
    exact B.ordered i j hij _ (List.head_mem (B.nonempty i)) _ (List.head_mem (B.nonempty j))
  have choice : ∃ i : Fin (k+1), |FiniteCuts.displacement q i|=1 ∧
      ((B.firstLabel i).val ≤ gap.val ↔ (B.firstLabel (q i)).val ≤ gap.val) := by
    by_cases hc : (B.firstLabel a).val ≤ gap.val ↔ (B.firstLabel b).val ≤ gap.val
    · refine ⟨a,?_,?_⟩
      · simpa only [FiniteCuts.displacement,habq] using hu
      · simpa only [habq] using hc
    · have hd : (B.firstLabel x).val ≤ gap.val ↔ (B.firstLabel y).val ≤ gap.val := by
        by_contra hd
        exact hneq (unit_cut_neighbor_unique (fun i => (B.firstLabel i).val) hfirst
          gap.val a b x y hu hv hc hd)
      refine ⟨x,?_,?_⟩
      · simpa only [FiniteCuts.displacement,hxyq] using hv
      · simpa only [hxyq] using hd
  obtain ⟨a,ha,hc⟩ := choice
  refine ⟨a,ha,?_⟩
  have hsame := hB a (B.lastLabel a) (List.getLast_mem (B.nonempty a))
    (B.firstLabel a) (List.head_mem (B.nonempty a))
  have hedge : P (B.lastLabel a)=B.firstLabel (q a) := B.edge a
  rw [hedge]
  exact hsame.trans hc

#print axioms protected_shallow_unit
end LRX.ContractionBlocks.System
