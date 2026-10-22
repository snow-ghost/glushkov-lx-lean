import LRX.CanonicalServiceFamily
import LRX.OrderedExactRoute
import LRX.TurningRoute

/-! Common assembly of exact retained-root and finite-child services. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem assemble_periodic_left_word (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hpart : CyclePart.IsPart selected p)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (ht : (services.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hprice : (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-discount)
    (finish : Fin n) (hports : ∀ a ∈ services, a.service.port.val ≤ finish.val)
    (a : ExactService n) (ha : a.service.port=0)
    (hat : a.service.target=CyclePart.remaining selected p hpart)
    (had : a.displacement=PrunedLift.displacement selected.supportᶜ d)
    (har : (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d (0)) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-discount+(finish.val : ℤ) := by
  have htargets : (services.map (fun a => a.service.target)).Pairwise Equiv.Perm.Disjoint :=
    List.pairwise_map.mpr hdis
  have hhead : ∀ c ∈ services, a.service.target.Disjoint c.service.target := by
    intro c hc
    have hs := Equiv.Perm.support_le_prod_of_mem
      (List.mem_map.mpr ⟨c,hc,rfl⟩) htargets
    rw [ht] at hs
    rw [hat]
    exact (CyclePart.remaining_disjoint selected p hpart).mono le_rfl hs
  have hall : (a::services).Pairwise (fun c e => c.service.target.Disjoint e.service.target) :=
    List.pairwise_cons.mpr ⟨hhead,hdis⟩
  have heval : ((a::services).map (fun a => a.service.target)).prod=p := by
    simp only [List.map_cons,List.prod_cons,hat,ht]
    exact CyclePart.remaining_product selected p hpart
  have hend : (fun i : Fin n => (i : ℤ)+((a::services).map (fun a => a.displacement i)).sum)=
      (fun i : Fin n => (i : ℤ)+d i) := by
    funext i
    have hs := canonical_family_displacement services hdis hc i
    rw [ht] at hs
    simp only [List.map_cons,List.sum_cons,had,hs,CyclePart.displacement_split selected d hfinite]
  obtain ⟨w,he,hl⟩ := ordered_reduced_route hn (a::services) hall finish (by
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [ha]
    · exact hports c hm)
  refine ⟨w,?_,?_⟩
  · rw [heval] at he
    exact he
  · rw [hend] at hl
    have hcast : ((((a::services).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)=
        ((a::services).map (fun c => (BufferProgram.rotations c.service.word : ℤ))).sum := by simp [Function.comp_def]
    have hl' : (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        ((((a::services).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)+
        (finish.val : ℤ) := by exact_mod_cast hl
    rw [hcast,List.map_cons,List.sum_cons,har,hprice] at hl'
    have hm := CyclePart.mass_split selected d hfinite
    linarith


theorem assemble_periodic_right_word (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n)
    (hpart : CyclePart.IsPart selected p)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (ht : (services.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hprice : (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-discount)
    (start finish : Fin n) (hs : start.val ≤ (r-1 : Fin n).val) (hf : finish.val ≤ (r-1 : Fin n).val)
    (hports : ∀ a ∈ services, start.val ≤ a.service.port.val ∧ a.service.port.val ≤ (r-1 : Fin n).val)
    (a : ExactService n) (ha : a.service.port=r-1)
    (hat : a.service.target=CyclePart.remaining selected p hpart)
    (had : a.displacement=PrunedLift.displacement selected.supportᶜ d)
    (har : (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d (r-1)) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-discount+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  have htargets : (services.map (fun a => a.service.target)).Pairwise Equiv.Perm.Disjoint :=
    List.pairwise_map.mpr hdis
  have hhead : ∀ c ∈ services, a.service.target.Disjoint c.service.target := by
    intro c hc
    have hsup := Equiv.Perm.support_le_prod_of_mem (List.mem_map.mpr ⟨c,hc,rfl⟩) htargets
    rw [ht] at hsup
    rw [hat]
    exact (CyclePart.remaining_disjoint selected p hpart).mono le_rfl hsup
  have hall : (a::services).Pairwise (fun c e => c.service.target.Disjoint e.service.target) :=
    List.pairwise_cons.mpr ⟨hhead,hdis⟩
  have heval : ((a::services).map (fun a => a.service.target)).prod=p := by
    simp only [List.map_cons,List.prod_cons,hat,ht]
    exact CyclePart.remaining_product selected p hpart
  have hdisp (i : Fin n) : ((a::services).map (fun a => a.displacement i)).sum=d i := by
    have hsum := canonical_family_displacement services hdis hc i
    rw [ht] at hsum
    simp only [List.map_cons,List.sum_cons,had,hsum,CyclePart.displacement_split selected d hfinite]
  obtain ⟨w,he,hl⟩ := ordered_turn_route hn hd (a::services) hall heval hdisp start finish (r-1) hs hf (by
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa only [ha] using And.intro hs (le_refl (r-1 : Fin n).val)
    · exact hports c hm)
  refine ⟨w,he,?_⟩
  have hcast : ((((a::services).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)=
      ((a::services).map (fun c => (BufferProgram.rotations c.service.word : ℤ))).sum := by simp [Function.comp_def]
  have hl' : (w.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      ((((a::services).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)+
      (((r-1 : Fin n).val-start.val : ℕ) : ℤ)+(((r-1 : Fin n).val-finish.val : ℕ) : ℤ) := by exact_mod_cast hl
  rw [hcast,List.map_cons,List.sum_cons,har,hprice,Nat.cast_sub hs,Nat.cast_sub hf] at hl'
  have hm := CyclePart.mass_split selected d hfinite
  linarith

#print axioms assemble_periodic_left_word
#print axioms assemble_periodic_right_word
end LRX.RotationWords
