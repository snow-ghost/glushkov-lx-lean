import LRX.ReducedRouteFrom
import LRX.OrderedExactRoute

/-! An ascending visit of ports followed by a return from the right boundary
has cursor cost at most (anchor-start)+(anchor-finish). -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem short_move_le_backward_difference (s t : Fin n) (h : t.val ≤ s.val) :
    min (t-s).val (n-(t-s).val) ≤ s.val-t.val := by
  by_cases he : t=s
  · subst t; rw [Fin.sub_val_of_le (show s ≤ s from le_rfl)]; simp
  · have hlt : t < s := by have : t.val ≠ s.val := fun hh => he (Fin.ext hh); omega
    have hv := Fin.coe_sub_iff_lt.mpr hlt
    have hm := min_le_right (t-s).val (n-(t-s).val)
    rw [hv] at hm
    have hs := s.isLt
    omega

theorem turning_walk_cost (s t anchor : Fin n) (services : List (ClosedService n))
    (hs : s.val ≤ anchor.val) (ht : t.val ≤ anchor.val)
    (horder : services.Pairwise (fun a b => a.port.val ≤ b.port.val))
    (hrange : ∀ a ∈ services, s.val ≤ a.port.val ∧ a.port.val ≤ anchor.val) :
    walkCost s t services ≤ (anchor.val-s.val)+(anchor.val-t.val) := by
  induction services generalizing s with
  | nil =>
    change min (t-s).val (n-(t-s).val) ≤ _
    by_cases h : s.val ≤ t.val
    · have := short_move_le_difference s t h; omega
    · have := short_move_le_backward_difference s t (by omega); omega
  | cons a rest ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp horder
    have ha := hrange a (by simp)
    have hw := ih a.port ha.2 htail
      (fun r hr => ⟨hhead r hr,(hrange r (by simp [hr])).2⟩)
    have hm := short_move_le_difference s a.port ha.1
    simp only [walkCost]
    omega

theorem ordered_turn_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (htarget : (services.map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ i, (services.map (fun a => a.displacement i)).sum=d i)
    (start finish anchor : Fin n) (hs : start.val ≤ anchor.val) (ht : finish.val ≤ anchor.val)
    (hrange : ∀ a ∈ services, start.val ≤ a.service.port.val ∧ a.service.port.val ≤ anchor.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      w.length ≤ LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+
        (anchor.val-start.val)+(anchor.val-finish.val) := by
  obtain ⟨ordered,hperm,ho⟩ := exists_ordered_exact_services services
  have hdo : ordered.Pairwise (fun a b => a.service.target.Disjoint b.service.target) :=
    (hperm.pairwise_iff (fun h => h.symm)).mp hdis
  have hto : (ordered.map (fun a => a.service.target)).prod=p := by
    rw [← Equiv.Perm.disjoint_prod_perm (List.pairwise_map.mpr hdis)
      (hperm.map (fun a => a.service.target))]
    exact htarget
  have hdisp' (i : Fin n) : (ordered.map (fun a => a.displacement i)).sum=d i := by
    rw [← (hperm.map (fun a => a.displacement i)).sum_eq]
    exact hdisp i
  obtain ⟨w,he,hl⟩ := reduced_route_from hn hd ordered hdo hto hdisp' start finish
  have hw := turning_walk_cost start finish anchor (ordered.map ExactService.service) hs ht
    (List.pairwise_map.mpr ho) (by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact hrange b (hperm.mem_iff.mpr hb))
  refine ⟨w,he,?_⟩
  rw [hl,← (hperm.map (fun a => BufferProgram.rotations a.service.word)).sum_eq]
  omega

#print axioms turning_walk_cost
#print axioms ordered_turn_route
end LRX.RotationWords
