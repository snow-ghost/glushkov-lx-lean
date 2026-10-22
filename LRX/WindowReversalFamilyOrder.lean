import LRX.WindowReversalServiceFamily

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts RotationWords
variable {n a b : ℕ} [NeZero n]

theorem separated_window_permutations_disjoint (A : Window n a) (B : Window n b)
    (hsep : A.offset+a ≤ B.offset) (p : State a) (q : State b) :
    (permutation A p).Disjoint (permutation B q) := by
  intro i
  by_cases hi : Contains A i
  · have hout : ¬Contains B i := by unfold Contains at hi ⊢; omega
    exact Or.inr (permutation_outside B q i hout)
  · exact Or.inl (permutation_outside A p i hi)

namespace ReversalServiceFamily
variable {W : Window n b} {right : Bool}

theorem reverse_targets_product (F : ReversalServiceFamily W right) :
    (F.list.reverse.map (fun s => s.service.target)).prod=permutation W Fin.revPerm := by
  rw [List.map_reverse]
  have hd := List.pairwise_map.mpr F.pairwise
  have hp := Equiv.Perm.disjoint_prod_perm hd (List.reverse_perm _).symm
  exact hp.symm.trans F.targets_product

theorem reverse_pairwise (F : ReversalServiceFamily W right) :
    F.list.reverse.Pairwise (fun s t => s.service.target.Disjoint t.service.target) := by
  apply List.pairwise_reverse.mpr
  exact F.pairwise.imp (fun h => h.symm)

theorem reverse_canonical (F : ReversalServiceFamily W right) :
    ∀ s ∈ F.list.reverse, ∀ i, s.displacement i=(s.service.target.symm i : ℤ)-(i : ℤ) := by
  intro s hs
  exact F.canonical s (List.mem_reverse.mp hs)

theorem reverse_rotations_sum (F : ReversalServiceFamily W right) :
    ((F.list.reverse.map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)=
      (b.choose 2 : ℤ)-(b/2 : ℕ) := by
  rw [List.map_reverse,List.sum_reverse]
  exact F.rotations_sum

theorem left_ordered (F : ReversalServiceFamily W false) :
    (F.list.map ExactService.service).Pairwise (fun s t => s.port.val ≤ t.port.val) := by
  apply List.pairwise_map.mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  rw [F.left_port_val,F.left_port_val]
  have h : i.val < j.val := hij
  omega

theorem right_reverse_ordered (F : ReversalServiceFamily W true) :
    (F.list.reverse.map ExactService.service).Pairwise (fun s t => s.port.val ≤ t.port.val) := by
  apply List.pairwise_map.mpr
  apply List.pairwise_reverse.mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  rw [F.right_port_val,F.right_port_val]
  have h : i.val < j.val := hij
  omega

theorem left_range (F : ReversalServiceFamily W false) (s : ExactService n) (hs : s ∈ F.list) :
    W.offset ≤ s.service.port.val ∧ s.service.port.val ≤ W.offset+(b/2-1) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
  rw [F.left_port_val]
  have := i.isLt
  omega

theorem right_range (F : ReversalServiceFamily W true) (s : ExactService n) (hs : s ∈ F.list) :
    W.offset+(b-1)/2 ≤ s.service.port.val ∧ s.service.port.val ≤ W.offset+b-2 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
  rw [F.right_port_val]
  have := i.isLt
  omega

end ReversalServiceFamily
#print axioms ReversalServiceFamily.right_reverse_ordered
end LRX.FiniteWindow
