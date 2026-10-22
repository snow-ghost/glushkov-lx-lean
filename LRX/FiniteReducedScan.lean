import LRX.FiniteExactFamily
import LRX.FiniteDisplacementSum
import LRX.FiniteCycleScan
import LRX.OrderedExactRoute

/-! A finite cycle scan priced by the inversions of the whole permutation. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ} [NeZero b]

theorem finite_reduced_left_scan (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (hd : l.Pairwise Equiv.Perm.Disjoint)
    (finish : Fin b) (hpos : ∀ q ∈ l, 0 < leftPeak q (finish.val+1)) :
    ∃ w : List Letter, eval w=l.prod⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (l.prod i : ℤ)) : ℤ)+
        (∑ i : Fin b, |displacement l.prod i|)-
        2*(l.map (fun q => (leftPeak q (finish.val+1) : ℤ))).sum+(finish.val : ℤ) := by
  obtain ⟨ss, ht, hdisp, hp, hc⟩ := left_peak_exact_family hb l hcycles
    (finish.val+1) (by omega) hpos
  have hdis : ss.Pairwise (fun a c => a.service.target.Disjoint c.service.target) := by
    apply List.pairwise_map.mp
    rw [ht]
    exact inverse_targets_disjoint l hd
  have hsum (i : Fin b) : (ss.map (fun a => a.displacement i)).sum=
      (l.map (fun q => displacement q i)).sum := by
    have h := congrArg (fun fs : List (Fin b → ℤ) => (fs.map (fun f => f i)).sum) hdisp
    simpa [List.map_map, Function.comp_def] using h
  have hend : (fun i : Fin b => (i : ℤ)+(ss.map (fun a => a.displacement i)).sum)=
      (fun i => (l.prod i : ℤ)) := by
    funext i
    rw [hsum, ← displacement_list_prod l hd]
    simp [displacement]
  obtain ⟨w, he, hl⟩ := ordered_reduced_route hb ss hdis finish (by
    intro a ha
    have := hp a ha
    omega)
  refine ⟨w, ?_, ?_⟩
  · rw [ht, inverse_cycle_product l hd] at he
    exact he
  · rw [hend] at hl
    have hcast : (((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℕ) : ℤ)=
        (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum := by
      simp [Function.comp_def]
    have hl' : (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (l.prod i : ℤ)) : ℤ)+
        (((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℕ) : ℤ)+
        (finish.val : ℤ) := by exact_mod_cast hl
    rw [hcast, hc] at hl'
    have hsplit :
        (l.map (fun q => (∑ i : Fin b, |displacement q i|)-2*(leftPeak q (finish.val+1) : ℤ))).sum=
        (l.map (fun q => ∑ i : Fin b, |displacement q i|)).sum-
          2*(l.map (fun q => (leftPeak q (finish.val+1) : ℤ))).sum := by
      clear hcycles hd hpos ht hdisp hp hc hsum hend he hl hl'
      induction l with
      | nil => simp
      | cons q rest ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
    rw [hsplit, ← displacement_mass_list_prod l hd] at hl'
    linarith

#print axioms finite_reduced_left_scan
end LRX.FiniteCuts
