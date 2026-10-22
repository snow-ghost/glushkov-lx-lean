import LRX.WindowReversalFamilyOrder

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts RotationWords
variable {n a b : ℕ} [NeZero n]

/-- Two adjacent reversal windows have an internal route of rotation cost at most
choose(a,2)+choose(b,2), from the first right center to the second left center. -/
theorem two_window_internal_word (hn : 2 ≤ n) (A : Window n a) (B : Window n b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hadj : B.offset=A.offset+a)
    (p : State n) (hbelow : FiniteRankOrder.Below p
      (permutation A Fin.revPerm*permutation B Fin.revPerm)) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨A.offset+(a-1)/2,by have := A.fits; omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨B.offset+(b/2-1),by have := B.fits; omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+(b.choose 2 : ℤ) := by
  classical
  obtain ⟨FA⟩ := exists_reversal_service_family hn A true
  obtain ⟨FB⟩ := exists_reversal_service_family hn B false
  let ss := FA.list.reverse++FB.list
  let start : Fin n := ⟨A.offset+(a-1)/2,by have := A.fits; omega⟩
  let finish : Fin n := ⟨B.offset+(b/2-1),by have := B.fits; omega⟩
  have hprod : (ss.map (fun s => s.service.target)).prod=
      permutation A Fin.revPerm*permutation B Fin.revPerm := by
    simp only [ss,List.map_append,List.prod_append,FA.reverse_targets_product,FB.targets_product]
  have hdis : ss.Pairwise (fun s t => s.service.target.Disjoint t.service.target) := by
    apply List.pairwise_append.mpr
    refine ⟨FA.reverse_pairwise,FB.pairwise,?_⟩
    intro s hs t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hs)
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    rw [FA.target_eq,FB.target_eq]
    exact separated_window_permutations_disjoint A B (by omega) _ _
  have hcan : ∀ s ∈ ss, ∀ i, s.displacement i=(s.service.target.symm i : ℤ)-(i : ℤ) := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact FA.reverse_canonical s hs
    · exact FB.canonical s hs
  have horder : (ss.map ExactService.service).Pairwise (fun s t => s.port.val ≤ t.port.val) := by
    rw [show ss.map ExactService.service=FA.list.reverse.map ExactService.service++FB.list.map ExactService.service
      by simp only [ss,List.map_append]]
    apply List.pairwise_append.mpr
    refine ⟨FA.right_reverse_ordered,FB.left_ordered,?_⟩
    intro s hs t ht
    obtain ⟨s0,hs0,rfl⟩ := List.mem_map.mp hs
    obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
    have hS := FA.right_range s0 (List.mem_reverse.mp hs0)
    have hT := FB.left_range t0 ht0
    omega
  have hrange : ∀ s ∈ ss.map ExactService.service,
      start.val ≤ s.port.val ∧ s.port.val ≤ finish.val := by
    intro s hs
    obtain ⟨s0,hs0,rfl⟩ := List.mem_map.mp hs
    change A.offset+(a-1)/2 ≤ s0.service.port.val ∧ s0.service.port.val ≤ B.offset+(b/2-1)
    rcases List.mem_append.mp hs0 with hs0 | hs0
    · have hS := FA.right_range s0 (List.mem_reverse.mp hs0)
      omega
    · have hS := FB.left_range s0 hs0
      omega
  have hw := ordered_walk_cost start finish (ss.map ExactService.service)
    (by dsimp [start,finish]; omega) horder hrange
  have hwalk : walkCost start finish (ss.map ExactService.service) ≤ a/2+b/2 := by
    change walkCost start finish (ss.map ExactService.service) ≤
      (B.offset+(b/2-1))-(A.offset+(a-1)/2) at hw
    omega
  have hsum : ((ss.map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)=
      (a.choose 2 : ℤ)+(b.choose 2 : ℤ)-(a/2 : ℕ)-(b/2 : ℕ) := by
    simp only [ss,List.map_append,List.sum_append,Nat.cast_add,FA.reverse_rotations_sum,FB.rotations_sum]
    ring
  have hp : FiniteRankOrder.Below p (ss.map (fun s => s.service.target)).prod := by rwa [hprod]
  obtain ⟨w,he,_,_,_,hlen⟩ := arbitrary_finite_route_rank_transfer hn ss hdis hcan p hp start finish
  have hr := route_rotations start finish (ss.map ExactService.service)
  simp only [List.map_map,Function.comp_def] at hr
  have hlenZ : (w.length : ℤ)=(inversionNumber p : ℤ)+
      (BufferProgram.rotations (route start finish (ss.map ExactService.service)) : ℤ) := by exact_mod_cast hlen
  have hrZ : (BufferProgram.rotations (route start finish (ss.map ExactService.service)) : ℤ)=
      ((ss.map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)+
      (walkCost start finish (ss.map ExactService.service) : ℤ) := by exact_mod_cast hr
  refine ⟨w,he,?_⟩
  omega

#print axioms two_window_internal_word
end LRX.FiniteWindow
