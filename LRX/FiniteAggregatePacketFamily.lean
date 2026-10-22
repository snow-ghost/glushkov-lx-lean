import LRX.FiniteWeightedPacketFamily

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Preserve the aggregate partial-peak discount supplied by a finite window
family; no per-service assignment of the local window parameters is needed. -/
theorem finite_aggregate_packet_family (hn : 2 ≤ n) (p selected : State n)
    (r port : Fin n) (hr : p.symm r ≠ r) (hport : port=r ∨ port+1=r)
    (hcover : PrunedLift.PacketCover p (displacement p.symm) r)
    (hpart : CyclePart.IsPart selected p)
    (hkeep : PrunedLift.KeepsCore p (displacement p.symm) r selected.supportᶜ)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss) (ht : (ss.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hp : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum ≤
      (∑ i, |displacement selected.symm i|)-discount) :
    ∃ a : ExactService n, a.service.port=port ∧ CanonicalFamily (a::ss) ∧
      (a::ss).Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      ((a::ss).map (fun a => a.service.target)).prod=p ∧
      (((a::ss).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i, |displacement p.symm i|)-portLoad (displacement p.symm) port-discount := by
  let saving : ExactService n → ℤ := fun a =>
    (∑ i, |a.displacement i|)-(BufferProgram.rotations a.service.word : ℤ)
  have hsave : (ss.map saving).sum=
      (ss.map (fun a => ∑ i, |a.displacement i|)).sum-
      (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum := by
    clear hdis hcan ht hp
    induction ss with
    | nil => simp
    | cons a rest ih => simp only [List.map_cons,List.sum_cons,saving] at ih ⊢; omega
  have hmass := canonical_family_mass ss hdis hcan
  rw [ht] at hmass
  have hmass' : (ss.map (fun a => ∑ i, |a.displacement i|)).sum=∑ i, |displacement selected.symm i| := hmass
  have hbound : discount ≤ (ss.map saving).sum := by rw [hsave,hmass']; omega
  obtain ⟨a,ha,hc,hd,ht',hr'⟩ := finite_weighted_packet_family hn p selected r port hr hport hcover
    hpart hkeep ss hdis hcan ht saving (by intro a ha; dsimp [saving]; omega)
  exact ⟨a,ha,hc,hd,ht',by omega⟩

#print axioms finite_aggregate_packet_family
end LRX.FiniteCuts
