import LRX.SourceSuffixDeficit
import LRX.JointInternalExternalBudget

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- One sum of all original source deficits, plus the exact cross-component
reserve in the external suffix, is paid by the global strict capacity. -/
theorem all_source_gap_cross_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (L : ℕ) (hL : (n+1)/2 < L) (hLn : L < n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L)
    (a : Fin n) (hlarge : (n+1)/2 < (componentSet p a).card) :
    2*(((positiveSourceFamily p n).map FillingWindow.deficit).sum+1) +
      2*((n-L).choose 2 : ℤ) -
      (∑ i : Fin (n-L), (((componentSet p (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)).card : ℤ)-1)) ≤
      2*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)) := by
  classical
  letI : NeZero (n-L) := ⟨by omega⟩
  let W : Window n (n-L) := ⟨L,by omega⟩
  let As := (positiveSourceFamily p n).filter (fun A => decide (A.window.offset < L))
  obtain ⟨hm,hd,_,hb⟩ := positive_source_family_spec p n
  have hmA : ∀ A ∈ As, A.Matches p.symm := fun A hA => hm A (List.mem_filter.mp hA).1
  have hdA : As.Pairwise FillingWindow.Apart := hd.filter _
  have hbA : ∀ A ∈ As, ∃ r : Fin n,
      r.val+1 = A.window.offset ∧ 0 < portLoad (displacement p.symm) r :=
    fun A hA => hb A (List.mem_filter.mp hA).1
  have hiA : ∀ A ∈ As, A.window.offset+A.size ≤ L := by
    intro A hA
    have hmem := (List.mem_filter.mp hA).1
    have hoff : A.window.offset < L := by simpa using (List.mem_filter.mp hA).2
    let r : Fin n := ⟨L-1,by omega⟩
    have hr : r.val+1 = L := by dsimp [r]; omega
    have hz : portLoad (displacement p.symm) r = 0 :=
      invariant_cut_port_zero p L (by omega) (by omega) hcut
    by_contra h
    have hh := positive_source_family_internal_ports p n A hmem r (by omega) (by omega)
    omega
  have hl : n-n/2 < (CycleFootprint.component (displacement p.symm) a).card := by
    change n-n/2 < (componentSet p a).card
    omega
  obtain ⟨f,hf,hbudget⟩ := joint_internal_external_strict_budget hn p.symm L (by omega) hL
    (invariant_cut_inverse p L hcut) As hmA hdA hiA hbA hmaj a hl
  have hI : inversionNumber p.symm = inversionNumber p := inversion_number_inverse p
  rw [hI] at hbudget
  have houter := source_suffix_deficit_reserve p W (by dsimp [W]; omega) f hf
  have hsplit (xs : List (FillingWindow n)) :
      ((xs.filter (fun A => decide (A.window.offset < L))).map FillingWindow.deficit).sum +
      ((xs.filter (fun A => decide (L ≤ A.window.offset))).map FillingWindow.deficit).sum =
      (xs.map FillingWindow.deficit).sum := by
    induction xs with
    | nil => simp
    | cons A xs ih =>
      by_cases h : A.window.offset < L
      · have hh : ¬L ≤ A.window.offset := by omega
        simp [h,hh,← ih,add_assoc]
      · have hh : L ≤ A.window.offset := by omega
        simp [h,hh,← ih,add_assoc,add_left_comm]
  have hs := hsplit (positiveSourceFamily p n)
  change ((As.map FillingWindow.deficit).sum +
    ((suffixSourceFamily p L).map FillingWindow.deficit).sum) = _ at hs
  change 2*((((n-L).choose 2 : ℤ)-(inversionNumber f : ℤ))) ≥
    2*((suffixSourceFamily p L).map FillingWindow.deficit).sum +
    2*((n-L).choose 2 : ℤ) -
    (∑ i : Fin (n-L), (((componentSet p (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)).card : ℤ)-1)) at houter
  linarith

#print axioms all_source_gap_cross_reserve
end LRX.FiniteCuts
