import LRX.ReversalPairCostSum
import LRX.ArbitraryFiniteRouteTransfer
import LRX.OrderedPortRoute

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The reversal is serviced by disjoint exact pairs in increasing left-port order. -/
theorem reversal_exact_service_family (hn : 2 ≤ n) :
    ∃ ss : List (ExactService n),
      (ss.map (fun s => s.service.target)).prod=Fin.revPerm ∧
      ss.Pairwise (fun s t => s.service.target.Disjoint t.service.target) ∧
      (∀ s ∈ ss, ∀ i, s.displacement i=(s.service.target.symm i : ℤ)-(i : ℤ)) ∧
      (ss.map ExactService.service).Pairwise (fun s t => s.port.val ≤ t.port.val) ∧
      (∀ s ∈ ss, s.service.port.val ≤ n/2-1) ∧
      ((ss.map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)=
        (n.choose 2 : ℤ)-(n/2 : ℕ) := by
  classical
  have hex (i : Fin (n/2)) := pair_left_exact_service hn (reversalLeft i) (reversalLeft i).rev
    (reversal_left_lt_right i)
  choose s hport htarget hdisp hrot using hex
  let ss := List.ofFn s
  have hmap : ss.map (fun a => a.service.target)=reversalPairs n := by
    simp only [ss,List.map_ofFn]
    congr 1
    funext i
    exact htarget i
  refine ⟨ss,?_,?_,?_,?_,?_,?_⟩
  · rw [hmap,reversal_pairs_product]
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    rw [htarget,htarget]
    exact reversal_pairs_disjoint i j (ne_of_lt hij)
  · intro a ha i
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    rw [hdisp,htarget]
    simp [displacement]
  · rw [show ss.map ExactService.service=List.ofFn (fun i => (s i).service) by simp [ss,Function.comp_def]]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    rw [hport,hport]
    exact le_of_lt hij
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    rw [hport]
    change i.val ≤ n/2-1
    have := i.isLt
    omega
  · simp only [ss,List.map_ofFn,List.sum_ofFn,Nat.cast_sum,Function.comp_def]
    simp_rw [hrot]
    exact reversal_pair_rotation_sum n

#print axioms reversal_exact_service_family
end LRX.FiniteCuts
