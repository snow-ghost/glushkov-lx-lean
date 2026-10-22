import LRX.CanonicalServiceFamily

namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem canonical_family_paid_bound (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (hprice : ∀ a ∈ services, (BufferProgram.rotations a.service.word : ℤ) ≤
      (∑ i : Fin n, |a.displacement i|)-2) :
    (services.map (fun (a : ExactService n) => (BufferProgram.rotations a.service.word : ℤ))).sum ≤
      (∑ i : Fin n, |((services.map (fun (a : ExactService n) => a.service.target)).prod.symm i : ℤ)-(i : ℤ)|)-
        2*(services.length : ℤ) := by
  rw [← canonical_family_mass services hdis hc]
  clear hdis hc
  induction services with
  | nil => simp
  | cons a rest ih =>
    have ha := hprice a (by simp)
    have hr := ih (fun b hb => hprice b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

theorem paid_packet_assembly {p selected : State n} {d : Fin n → ℤ}
    (hpart : CyclePart.IsPart selected p)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services) (ht : (services.map (fun (a : ExactService n) => a.service.target)).prod=selected)
    (hprice : ∀ a ∈ services, (BufferProgram.rotations a.service.word : ℤ) ≤
      (∑ i : Fin n, |a.displacement i|)-2)
    (a : ExactService n) (hat : a.service.target=CyclePart.remaining selected p hpart)
    (had : a.displacement=PrunedLift.displacement selected.supportᶜ d) (load : ℤ)
    (har : (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-load) :
    (a::services).Pairwise (fun c e => c.service.target.Disjoint e.service.target) ∧
    ((a::services).map (fun (c : ExactService n) => c.service.target)).prod=p ∧
    (∀ i, ((a::services).map (fun (c : ExactService n) => c.displacement i)).sum=d i) ∧
    (((a::services).map (fun (c : ExactService n) => BufferProgram.rotations c.service.word)).sum : ℤ) ≤
      (∑ i : Fin n, |d i|)-load-2*(services.length : ℤ) := by
  have htargets := List.pairwise_map.mpr hdis
  have hhead : ∀ c ∈ services, a.service.target.Disjoint c.service.target := by
    intro c hc
    have hs := Equiv.Perm.support_le_prod_of_mem (List.mem_map.mpr ⟨c,hc,rfl⟩) htargets
    rw [ht] at hs
    rw [hat]
    exact (CyclePart.remaining_disjoint selected p hpart).mono le_rfl hs
  refine ⟨List.pairwise_cons.mpr ⟨hhead,hdis⟩,?_,?_,?_⟩
  · simp only [List.map_cons,List.prod_cons,hat,ht]
    exact CyclePart.remaining_product selected p hpart
  · intro i
    have hs := canonical_family_displacement services hdis hc i
    rw [ht] at hs
    simp only [List.map_cons,List.sum_cons,had,hs,CyclePart.displacement_split selected d hfinite]
  · have hs := canonical_family_paid_bound services hdis hc hprice
    rw [ht] at hs
    have hm := CyclePart.mass_split selected d hfinite
    have hcast : (((services.map (fun (c : ExactService n) => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)=
        (services.map (fun (c : ExactService n) => (BufferProgram.rotations c.service.word : ℤ))).sum := by simp [Function.comp_def]
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,har,hcast]
    omega

#print axioms paid_packet_assembly
end LRX.RotationWords
