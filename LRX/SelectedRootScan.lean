import LRX.CycleSelection

/-! A full finite target is served by automatically selecting available child
cycles and putting every other cycle into the enclosing root service. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ} [NeZero b]

theorem selected_root_scan (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (hd : l.Pairwise Equiv.Perm.Disjoint)
    (hroot : l.prod 0 ≠ 0) (u v : Fin b)
    (hu : Equiv.Perm.SameCycle l.prod 0 u) (hv : Equiv.Perm.SameCycle l.prod 0 v)
    (hinside : ∀ i, l.prod i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val) (finish : Fin b) :
    ∃ w : List Letter, eval w=l.prod⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (l.prod i : ℤ)) : ℤ)+
        (∑ i : Fin b, |displacement l.prod i|)-portLoad (displacement l.prod) 0-
        2*((selectedCycles l (finish.val+1)).map
          (fun q => (leftPeak q (finish.val+1) : ℤ))).sum+(finish.val : ℤ) := by
  let y := finish.val+1
  let root := (remainingCycles l y).prod⁻¹
  have hr : root 0 ≠ 0 := by
    intro h
    have he := congrArg (remainingCycles l y).prod h
    exact remaining_moves_root l hd hroot y (by simpa [root] using he.symm)
  have hp : (root⁻¹::selectedCycles l y).prod=l.prod := by
    simpa only [root,inv_inv] using selection_product l hd y
  have hdis : (root⁻¹::selectedCycles l y).Pairwise Equiv.Perm.Disjoint := by
    simpa only [root,inv_inv] using selection_disjoint l hd y
  have hc : ∀ q ∈ selectedCycles l y, q.IsCycle := by
    intro q hq
    exact hcycles q ((selected_mem l y q).mp hq).1
  obtain ⟨w,he,hl⟩ := root_and_children_scan hb root (selectedCycles l y) hc hdis hr u v
    (by rw [hp]; exact hu) (by rw [hp]; exact hv) (by rw [hp]; exact hinside) finish
    (fun q hq => ((selected_mem l y q).mp hq).2.2)
  rw [hp] at he hl
  exact ⟨w,he,hl⟩

#print axioms selected_root_scan
end LRX.FiniteCuts
