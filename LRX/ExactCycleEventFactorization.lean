import LRX.ZeroGapCycleRoots
import LRX.FiniteCycleSupportBudget
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def cycleEventWord (p : State n) : List (Event n) :=
  List.zipWith (fun a b => (a,b)) (p.toList (cycleRoot p)) (p.toList (cycleRoot p)).tail

theorem cycle_event_word_product (p : State n) (hp : p.IsCycle) :
    ((cycleEventWord p).map eventSwap).prod = p := by
  have hm := cycle_root_mem hp
  have he : p.cycleOf (cycleRoot p) = p := hp.cycleOf_eq (Equiv.Perm.mem_support.mp hm)
  change ((List.zipWith (fun a b => (a,b)) _ _).map eventSwap).prod = p
  rw [List.map_zipWith]
  change (p.toList (cycleRoot p)).formPerm = p
  rw [Equiv.Perm.formPerm_toList,he]

theorem cycle_event_word_length (p : State n) (hp : p.IsCycle) :
    (cycleEventWord p).length+1 = p.support.card := by
  have hm := cycle_root_mem hp
  have he : p.cycleOf (cycleRoot p) = p := hp.cycleOf_eq (Equiv.Perm.mem_support.mp hm)
  have hc := hp.two_le_card_support
  simp only [cycleEventWord,List.length_zipWith,List.length_tail,Equiv.Perm.length_toList,he]
  omega

noncomputable def exactEventWord (p : State n) : List (Event n) :=
  p.cycleFactorsFinset.toList.flatMap cycleEventWord

/-- The actual disjoint cycles give a transposition factorization of exact reflection rank. -/
theorem exact_event_word_spec (p : State n) :
    ((exactEventWord p).map eventSwap).prod = p ∧
      (exactEventWord p).length+p.cycleFactorsFinset.card = p.support.card := by
  classical
  have hcycles := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset (σ := p)
    (Finset.nodup_toList p.cycleFactorsFinset)).mp (by simp)
  constructor
  · unfold exactEventWord
    rw [List.map_flatMap,List.flatMap_def,List.prod_flatten,List.map_map]
    have he : (p.cycleFactorsFinset.toList.map (fun q => ((cycleEventWord q).map eventSwap).prod)) =
        p.cycleFactorsFinset.toList := by
      calc
        _ = p.cycleFactorsFinset.toList.map (fun q => q) := by
          apply List.map_congr_left
          intro q hq
          exact cycle_event_word_product q (hcycles.1 q hq)
        _ = _ := List.map_id' _
    simp only [Function.comp_def]
    rw [he]
    exact hcycles.2.2
  · have hsum : (∑ q ∈ p.cycleFactorsFinset, ((cycleEventWord q).length+1)) = p.support.card := by
      calc
        _ = ∑ q ∈ p.cycleFactorsFinset, q.support.card := by
          apply Finset.sum_congr rfl
          intro q hq
          exact cycle_event_word_length q (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
        _ = _ := FiniteCuts.cycle_support_card_sum p
    simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] at hsum
    have hs := List.sum_toFinset (fun q : State n => (cycleEventWord q).length)
      (Finset.nodup_toList p.cycleFactorsFinset)
    simp only [Finset.toList_toFinset] at hs
    simp only [exactEventWord,List.length_flatMap]
    rw [← hs]
    exact hsum

#print axioms cycle_event_word_product
#print axioms exact_event_word_spec
end LRX.ZeroGap
