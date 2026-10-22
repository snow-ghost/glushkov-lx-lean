import LRX.WindowPairExactService

namespace LRX.FiniteWindow
open scoped BigOperators Fin.NatCast Fin.CommRing
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

/-- Exact ambient services for every pair of a local reversal, at either incident side. -/
structure ReversalServiceFamily (W : Window n b) (right : Bool) where
  service : Fin (b/2) → ExactService n
  port_eq : ∀ i, (service i).service.port=
    if right then embed W (reversalLeft i).rev-1 else embed W (reversalLeft i)
  target_eq : ∀ i, (service i).service.target=permutation W (reversalPair i)
  displacement_eq : ∀ i, (service i).displacement=displacement (permutation W (reversalPair i))
  rotations_eq : ∀ i, (BufferProgram.rotations (service i).service.word : ℤ)=
    2*(((reversalLeft i).rev : ℤ)-(reversalLeft i : ℤ))-2

theorem exists_reversal_service_family (hn : 2 ≤ n) (W : Window n b) (right : Bool) :
    Nonempty (ReversalServiceFamily W right) := by
  classical
  have hex (i : Fin (b/2)) : ∃ s : ExactService n,
      s.service.port=(if right then embed W (reversalLeft i).rev-1 else embed W (reversalLeft i)) ∧
      s.service.target=permutation W (reversalPair i) ∧
      s.displacement=displacement (permutation W (reversalPair i)) ∧
      (BufferProgram.rotations s.service.word : ℤ)=2*(((reversalLeft i).rev : ℤ)-(reversalLeft i : ℤ))-2 := by
    cases right with
    | false => exact window_pair_left_exact_service hn W _ _ (reversal_left_lt_right i)
    | true => exact window_pair_right_exact_service hn W _ _ (reversal_left_lt_right i)
  choose s hp ht hd hr using hex
  exact ⟨⟨s,hp,ht,hd,hr⟩⟩

namespace ReversalServiceFamily
variable {W : Window n b} {right : Bool}

def list (F : ReversalServiceFamily W right) : List (ExactService n) := List.ofFn F.service

theorem targets_product (F : ReversalServiceFamily W right) :
    (F.list.map (fun s => s.service.target)).prod=permutation W Fin.revPerm := by
  have hm : F.list.map (fun s => s.service.target)=(reversalPairs b).map (permutation W) := by
    simp only [list,reversalPairs,List.map_ofFn]
    congr 1
    funext i
    exact F.target_eq i
  rw [hm,← permutation_list_prod,reversal_pairs_product]

theorem pairwise (F : ReversalServiceFamily W right) :
    F.list.Pairwise (fun s t => s.service.target.Disjoint t.service.target) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  rw [F.target_eq,F.target_eq]
  exact permutation_disjoint W _ _ (reversal_pairs_disjoint i j (ne_of_lt hij))

theorem canonical (F : ReversalServiceFamily W right) :
    ∀ s ∈ F.list, ∀ i, s.displacement i=(s.service.target.symm i : ℤ)-(i : ℤ) := by
  intro s hs i
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
  rw [F.displacement_eq,F.target_eq]
  simp [displacement,permutation_symm,reversalPair]

theorem rotations_sum (F : ReversalServiceFamily W right) :
    ((F.list.map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)=
      (b.choose 2 : ℤ)-(b/2 : ℕ) := by
  simp only [list,List.map_ofFn,List.sum_ofFn,Nat.cast_sum,Function.comp_def]
  simp_rw [F.rotations_eq]
  exact reversal_pair_rotation_sum b

theorem left_port_val (F : ReversalServiceFamily W false) (i : Fin (b/2)) :
    (F.service i).service.port.val=W.offset+i.val := by
  rw [F.port_eq]
  rfl

theorem right_port_val (F : ReversalServiceFamily W true) (i : Fin (b/2)) :
    (F.service i).service.port.val=W.offset+(b-2-i.val) := by
  have hi := i.isLt
  have hlt := reversal_left_lt_right i
  have hz : embed W (reversalLeft i).rev ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [embed,Fin.val_zero,Fin.val_rev,reversalLeft] at hv hlt
    omega
  rw [F.port_eq]
  simp only [Bool.true_eq,ite_true]
  rw [Fin.val_sub_one_of_ne_zero hz]
  simp only [embed,Fin.val_rev,reversalLeft]
  omega

end ReversalServiceFamily
#print axioms exists_reversal_service_family
#print axioms ReversalServiceFamily.targets_product
#print axioms ReversalServiceFamily.rotations_sum
end LRX.FiniteWindow
