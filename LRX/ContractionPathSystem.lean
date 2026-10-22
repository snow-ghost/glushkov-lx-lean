import LRX.ContractionBlockLists

namespace LRX.ContractionBlocks
variable {m k : ℕ}

/-- Ordered, disjoint paths covering the original labels. The current
permutation joins their ends using actual original arrows. -/
structure System (P : State m) (q : State k) where
  nodes : Fin k → List (Fin m)
  nonempty : ∀ i, nodes i ≠ []
  nodup : ∀ i, (nodes i).Nodup
  chain : ∀ i, (nodes i).IsChain (fun x y => P x=y)
  cover : ∀ x : Fin m, ∃ i : Fin k, x ∈ nodes i
  ordered : ∀ (i j : Fin k), i.val < j.val → ∀ x ∈ nodes i, ∀ y ∈ nodes j, x.val < y.val
  edge : ∀ i : Fin k, P ((nodes i).getLast (nonempty i))=(nodes (q i)).head (nonempty (q i))

namespace System

def initial (P : State m) : System P P where
  nodes i := [i]
  nonempty i := by simp
  nodup i := by simp
  chain i := by simp
  cover x := ⟨x,by simp⟩
  ordered i j hij x hx y hy := by
    simp only [List.mem_singleton] at hx hy
    subst x; subst y
    exact hij
  edge i := by simp

theorem nodes_distinct {P : State m} {q : State k} (B : System P q)
    (i j : Fin k) (hij : i ≠ j) {x y : Fin m} (hx : x ∈ B.nodes i) (hy : y ∈ B.nodes j) : x ≠ y := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  intro hxy
  have hv := congrArg Fin.val hxy
  by_cases hlt : i.val < j.val
  · have h := B.ordered i j hlt x hx y hy
    omega
  · have h := B.ordered j i (by omega) y hy x hx
    omega

/-- Merge the selected two paths while performing the exact previously
verified row/column contraction of the current permutation. -/
def contract {P : State m} {q : State (k+1)} (B : System P q)
    (a : Fin (k+1)) (hadj : |FiniteCuts.displacement q a|=1) : System P (FiniteCuts.contract q a) := by
  have hneq : q a ≠ a := by intro h; simp [FiniteCuts.displacement,h] at hadj
  refine {
    nodes := mergeLists B.nodes a (q a)
    nonempty := merge_nonempty B.nodes B.nonempty a (q a)
    nodup := ?_
    chain := ?_
    cover := ?_
    ordered := ?_
    edge := ?_ }
  · intro i
    unfold mergeLists
    split_ifs
    · apply List.nodup_append.mpr
      exact ⟨B.nodup a,B.nodup (q a),fun x hx y hy => B.nodes_distinct a (q a) (Ne.symm hneq) hx hy⟩
    · exact B.nodup _
  · intro i
    unfold mergeLists
    split_ifs
    · apply (B.chain a).append (B.chain (q a))
      intro x hx y hy
      simp only [List.getLast?_eq_getLast (B.nonempty a),Option.mem_some_iff] at hx
      simp only [List.head?_eq_head (B.nonempty (q a)),Option.mem_some_iff] at hy
      subst x; subst y
      exact B.edge a
    · exact B.chain _
  · intro x
    obtain ⟨s,hs⟩ := B.cover x
    by_cases hsa : s=a
    · subst s
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hneq
      exact ⟨i,(merge_membership B.nodes a (q a) i x).mpr ⟨a,Or.inr ⟨rfl,hi⟩,hs⟩⟩
    · obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hsa
      exact ⟨i,(merge_membership B.nodes a (q a) i x).mpr ⟨s,Or.inl hi.symm,hs⟩⟩
  · intro i j hij x hx y hy
    obtain ⟨s,hs,hxs⟩ := (merge_membership B.nodes a (q a) i x).mp hx
    obtain ⟨t,ht,hyt⟩ := (merge_membership B.nodes a (q a) j y).mp hy
    exact B.ordered s t (contributor_order a (q a) hadj i j hij s t hs ht) x hxs y hyt
  · intro i
    rw [merged_last,merged_head B.nodes B.nonempty a (q a) hadj]
    simpa only [FiniteCuts.contract_entry] using B.edge (a.succAbove i)

#print axioms contract
end System
end LRX.ContractionBlocks
