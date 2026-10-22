import LRX.FiniteCycleRoutes
import LRX.OrderedPortRoute

/-! A paid monotone scan of the finite cycles accessible from the left.
The list contains actual disjoint cycles and every service word is constructed. -/
namespace LRX.FiniteCuts
open RotationWords
variable {b : ℕ} [NeZero b]

omit [NeZero b] in
theorem inverse_targets_disjoint (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (fun q => q⁻¹)).Pairwise Equiv.Perm.Disjoint := by
  exact List.pairwise_map.mpr (hd.imp (fun h => h.inv_left.inv_right))

omit [NeZero b] in
theorem inverse_cycle_product (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (fun q => q⁻¹)).prod=l.prod⁻¹ := by
  rw [List.prod_inv_reverse]
  exact Equiv.Perm.disjoint_prod_perm (inverse_targets_disjoint l hd) (List.reverse_perm _).symm

theorem left_cycle_scan (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (hd : l.Pairwise Equiv.Perm.Disjoint)
    (finish : Fin b) (hpos : ∀ q ∈ l, 0 < leftPeak q (finish.val+1)) :
    ∃ w : List Letter, eval w=l.prod⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (l.map (fun q => cycleBasePrice q-2*(leftPeak q (finish.val+1) : ℤ))).sum+
        (finish.val : ℤ) := by
  obtain ⟨ss, ht, hp, hc⟩ := left_peak_services hb l hcycles (finish.val+1)
    (by omega) hpos
  have hdis : ss.Pairwise (fun a c => Disjoint a.target.support c.target.support) := by
    have hh : (ss.map ClosedService.target).Pairwise Equiv.Perm.Disjoint := by
      rw [ht]
      exact inverse_targets_disjoint l hd
    exact (List.pairwise_map.mp hh).imp
      (fun h => Equiv.Perm.disjoint_iff_disjoint_support.mp h)
  obtain ⟨w, hw, hlen⟩ := interval_route 0 finish ss (by simp) hdis (by
    intro s hs
    have := hp s hs
    simp only [Fin.val_zero]
    omega)
  refine ⟨w, ?_, ?_⟩
  · simpa [ht, inverse_cycle_product l hd, RotationWords.rotation] using hw
  · have hz : (((ss.map (fun s => s.word.length)).sum : ℕ) : ℤ)=
        (ss.map (fun s => (s.word.length : ℤ))).sum := by simp [Function.comp_def]
    have hh : (w.length : ℤ) ≤
        (((ss.map (fun s => s.word.length)).sum : ℕ) : ℤ)+(finish.val : ℤ) := by
      exact_mod_cast (by simpa using hlen : w.length ≤ (ss.map (fun s => s.word.length)).sum+finish.val)
    rwa [hz, hc] at hh

#print axioms inverse_cycle_product
#print axioms left_cycle_scan
end LRX.FiniteCuts
