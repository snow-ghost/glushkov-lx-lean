import LRX.AllSourceGapCrossReserve
import LRX.LargeComponentJointBudget

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- Multiple nontrivial components leave a nonempty exterior for each component. -/
theorem component_card_lt_of_multiple_roots (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (a : Fin n) : (componentSet p a).card < n := by
  classical
  by_contra h
  have hU : componentSet p a = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  have hp (i : Fin n) : CycleFootprint.LoadPath (displacement p.symm) a i := by
    apply (CycleFootprint.mem_component _ _ _).mp
    change i ∈ componentSet p a
    rw [hU]
    exact Finset.mem_univ _
  have hc : (componentRoots p).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    exact component_roots_unique p hu hv ((CycleFootprint.load_path_symm _ (hp u)).trans (hp v))
  omega

/-- Cross reserve for all original gaps at the actual large-component cut.
The cut, the nonempty exterior and all window certificates are derived. -/
theorem large_component_cross_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (a : Fin n)
    (hlarge : (n+1)/2 < (componentSet p a).card) :
    let q := localTarget p 0 (componentLeft p a)
    let L := (componentSet p a).card
    2*(((positiveSourceFamily q n).map FillingWindow.deficit).sum+1) +
      2*((n-L).choose 2 : ℤ) -
      (∑ i : Fin (n-L), (((componentSet q (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)).card : ℤ)-1)) ≤
      2*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)) := by
  let r := componentLeft p a
  let q := localTarget p 0 r
  let L := (componentSet p a).card
  have hLn : L < n := component_card_lt_of_multiple_roots p hm a
  obtain ⟨hcut,hcards⟩ := component_recenter_cut p a
  have hz := component_left_port_zero p a
  have hr : componentLeft p a-1+1 = r := by dsimp [r]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 (componentLeft p a-1) hd hmaj hz
  rw [hr] at hqm
  have hc : (componentSet q (a-r)).card = L := by
    have h := hcards (a-r)
    simpa only [r,q,L,sub_add_cancel] using h
  have hqlarge : (n+1)/2 < (componentSet q (a-r)).card := by rw [hc]; exact hlarge
  have hI := inversion_number_zero_recenter p (componentLeft p a-1) hz
  rw [hr] at hI
  have h := all_source_gap_cross_reserve hn q hqm L hlarge hLn hcut (a-r) hqlarge
  rw [hI] at h
  exact h

#print axioms component_card_lt_of_multiple_roots
#print axioms large_component_cross_reserve
end LRX.FiniteCuts
