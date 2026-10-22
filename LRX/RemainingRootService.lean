import LRX.SelectedCycleSplit

/-! The remaining factor supplies an exact root service, with the original
root-port discount, when the full finite target has an enclosing root cycle. -/
namespace LRX.PrunedLift
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem remaining_root_service (hn : 2 ≤ n) (root selected : State n)
    (hd : root.Disjoint selected) (hroot : root 0 ≠ 0) (u v : Fin n)
    (hu : ((root*selected)⁻¹).SameCycle 0 u)
    (hv : ((root*selected)⁻¹).SameCycle 0 v)
    (hinside : ∀ i, ((root*selected)⁻¹) i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=root ∧
      a.displacement=(fun i => (root.symm i : ℤ)-(i : ℤ)) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |(root.symm i : ℤ)-(i : ℤ)|)-
          portLoad (fun i => ((root*selected).symm i : ℤ)-(i : ℤ)) 0 := by
  have hkeep := keep_root_zero root selected hd hroot
  have hfix : selected 0=0 := (hd 0).resolve_left hroot
  have hm : ((root*selected)⁻¹) 0 ≠ 0 := by
    intro h
    apply hroot
    have he := congrArg (root*selected) h
    simpa [Equiv.Perm.mul_apply,hfix] using he.symm
  obtain ⟨a,hport,ht,hdisp,hprice⟩ := enclosing_pruned_exact_service hn (root*selected)
    hm u v hu hv hinside selected.supportᶜ (selected_complement_invariant root selected hd) hkeep
  rw [canonical_pruned_port_load (root*selected) selected.supportᶜ
    (selected_complement_invariant root selected hd) hkeep, retained_displacement root selected hd] at hprice
  rw [retained_factor root selected hd] at ht
  rw [retained_displacement root selected hd] at hdisp
  exact ⟨a,hport,ht,hdisp,hprice⟩

#print axioms remaining_root_service
end LRX.PrunedLift
