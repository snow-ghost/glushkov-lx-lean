import LRX.RootAndChildrenScan

/-! Select available nonroot cycles; all other cycles remain in the root factor. -/
namespace LRX.FiniteCuts
variable {b : ℕ} [NeZero b]

def availableCycle (y : ℕ) (q : State b) : Bool := decide (q 0=0 ∧ 0 < leftPeak q y)

def selectedCycles (l : List (State b)) (y : ℕ) : List (State b) := l.filter (availableCycle y)

def remainingCycles (l : List (State b)) (y : ℕ) : List (State b) :=
  l.filter (fun q => !(availableCycle y q))

theorem selected_mem (l : List (State b)) (y : ℕ) (q : State b) :
    q ∈ selectedCycles l y ↔ q ∈ l ∧ q 0=0 ∧ 0 < leftPeak q y := by
  simp [selectedCycles,availableCycle]

omit [NeZero b] in
theorem product_fixes (l : List (State b)) (i : Fin b) (h : ∀ q ∈ l, q i=i) : l.prod i=i := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.prod_cons,Equiv.Perm.mul_apply,ih (fun r hr => h r (by simp [hr]))]
    exact h q (by simp)

theorem selection_partition (l : List (State b)) (y : ℕ) :
    (remainingCycles l y ++ selectedCycles l y).Perm l := by
  have h := List.filter_append_perm (availableCycle y) l
  exact (List.perm_append_comm).trans h

theorem selection_disjoint (l : List (State b)) (hd : l.Pairwise Equiv.Perm.Disjoint) (y : ℕ) :
    ((remainingCycles l y).prod::selectedCycles l y).Pairwise Equiv.Perm.Disjoint := by
  have hpair : (remainingCycles l y ++ selectedCycles l y).Pairwise Equiv.Perm.Disjoint :=
    ((selection_partition l y).pairwise_iff (fun h => h.symm)).mpr hd
  obtain ⟨hr,hs,hcross⟩ := List.pairwise_append.mp hpair
  apply List.pairwise_cons.mpr
  refine ⟨?_,hs⟩
  intro q hq
  exact (Equiv.Perm.disjoint_prod_right (remainingCycles l y)
    (fun r hr => (hcross r hr q hq).symm)).symm

theorem selection_product (l : List (State b)) (hd : l.Pairwise Equiv.Perm.Disjoint) (y : ℕ) :
    ((remainingCycles l y).prod::selectedCycles l y).prod=l.prod := by
  have h := Equiv.Perm.disjoint_prod_perm hd (selection_partition l y).symm
  simpa only [List.prod_append,List.prod_cons] using h.symm

theorem remaining_moves_root (l : List (State b)) (hd : l.Pairwise Equiv.Perm.Disjoint)
    (hmove : l.prod 0 ≠ 0) (y : ℕ) : (remainingCycles l y).prod 0 ≠ 0 := by
  have hs : (selectedCycles l y).prod 0=0 :=
    product_fixes _ _ (fun q hq => ((selected_mem l y q).mp hq).2.1)
  intro hr
  apply hmove
  rw [← selection_product l hd y,List.prod_cons,Equiv.Perm.mul_apply,hs,hr]

#print axioms selection_product
#print axioms selection_disjoint
#print axioms remaining_moves_root
end LRX.FiniteCuts
