import LRX.TurningRoute

/-! Exact services can be ordered along either directed circular arc;
the paid cursor walk costs at most the arc length. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def arcCoordinate (forward : Bool) (root i : Fin n) : Fin n :=
  if forward then i-root else root-i

theorem arc_move_le_difference (forward : Bool) (root s t : Fin n)
    (h : (arcCoordinate forward root s).val ≤ (arcCoordinate forward root t).val) :
    min (t-s).val (n-(t-s).val) ≤
      (arcCoordinate forward root t).val-(arcCoordinate forward root s).val := by
  cases forward
  · have he : t-s=(root-s)-(root-t) := by ring
    rw [he]
    exact short_move_le_backward_difference (root-t) (root-s) h
  · have he : t-s=(t-root)-(s-root) := by ring
    rw [he]
    exact short_move_le_difference (s-root) (t-root) h

theorem arc_walk_cost (forward : Bool) (root s t : Fin n) (services : List (ClosedService n))
    (hst : (arcCoordinate forward root s).val ≤ (arcCoordinate forward root t).val)
    (horder : services.Pairwise (fun a b =>
      (arcCoordinate forward root a.port).val ≤ (arcCoordinate forward root b.port).val))
    (hrange : ∀ a ∈ services, (arcCoordinate forward root s).val ≤ (arcCoordinate forward root a.port).val ∧
      (arcCoordinate forward root a.port).val ≤ (arcCoordinate forward root t).val) :
    walkCost s t services ≤ (arcCoordinate forward root t).val-(arcCoordinate forward root s).val := by
  induction services generalizing s with
  | nil => exact arc_move_le_difference forward root s t hst
  | cons a rest ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp horder
    have ha := hrange a (by simp)
    have hw := ih a.port ha.2 htail (fun b hb => ⟨hhead b hb,(hrange b (by simp [hb])).2⟩)
    have hm := arc_move_le_difference forward root s a.port ha.1
    simp only [walkCost]
    omega

theorem arc_ordered_services (forward : Bool) (root : Fin n) (services : List (ExactService n)) :
    ∃ ordered : List (ExactService n), services.Perm ordered ∧
      ordered.Pairwise (fun a b => (arcCoordinate forward root a.service.port).val ≤
        (arcCoordinate forward root b.service.port).val) := by
  let key : ExactService n → ℕ := fun a => (arcCoordinate forward root a.service.port).val
  let le : ExactService n → ExactService n → Bool := fun a b => key a ≤ key b
  refine ⟨services.mergeSort le,(List.mergeSort_perm services le).symm,?_⟩
  have htrans : ∀ a b c, le a b → le b c → le a c := by
    intro a b c hab hbc
    simp only [le,decide_eq_true_eq] at *
    exact Nat.le_trans hab hbc
  have htotal : ∀ a b, le a b || le b a := by
    intro a b
    simp only [le,Bool.or_eq_true,decide_eq_true_eq]
    exact Nat.le_total (key a) (key b)
  simpa only [le,key,decide_eq_true_eq] using List.pairwise_mergeSort (le := le) htrans htotal services

theorem circular_reduced_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (forward : Bool) (start finish : Fin n)
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (htarget : (services.map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ i, (services.map (fun a => a.displacement i)).sum=d i)
    (hrange : ∀ a ∈ services, (arcCoordinate forward start a.service.port).val ≤
      (arcCoordinate forward start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      w.length ≤ LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+
        (arcCoordinate forward start finish).val := by
  obtain ⟨ordered,hperm,ho⟩ := arc_ordered_services forward start services
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
  have hz : arcCoordinate forward start start=0 := by cases forward <;> simp [arcCoordinate]
  have hw := arc_walk_cost forward start start finish (ordered.map ExactService.service)
    (by rw [hz]; exact Nat.zero_le _) (List.pairwise_map.mpr ho) (by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact ⟨by rw [hz]; exact Nat.zero_le _,hrange b (hperm.mem_iff.mpr hb)⟩)
  rw [hz,Fin.val_zero,Nat.sub_zero] at hw
  have hrot := (hperm.map (fun a => BufferProgram.rotations a.service.word)).sum_eq
  exact ⟨w,he,by omega⟩

#print axioms arc_walk_cost
#print axioms circular_reduced_route
end LRX.RotationWords
