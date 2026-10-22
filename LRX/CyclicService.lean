import LRX.FullCycleService

/-! Canonical cycle extraction eliminates the itinerary witness from the public
service theorem. The constructed word covers a single cycle with full support.
Its X count is raw; this is not yet the sharp diameter upper theorem. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem follows_iff_isChain (p : State n) (path : List (Fin n)) :
    Follows p path ↔ path.IsChain (fun a b => (p⁻¹) a=b) := by
  induction path with
  | nil => simp [Follows]
  | cons a rest ih =>
    cases rest with
    | nil => simp [Follows]
    | cons b rest =>
      change ((p⁻¹) a=b ∧ Follows p (b::rest)) ↔ _
      rw [List.isChain_cons_cons, ih]

theorem exists_complete_cycle_order {p : State n}
    (hc : (p⁻¹).IsCycle) (hs : (p⁻¹).support=Finset.univ) :
    ∃ rest : List (Fin n),
      ((0 : Fin n)::rest).Nodup ∧
      (∀ i : Fin n, i ∈ (0 : Fin n)::rest) ∧
      Follows p ((0 : Fin n)::rest) ∧
      (p⁻¹) (((0 : Fin n)::rest).getLast (by simp))=0 := by
  have hxmem : (0 : Fin n) ∈ (p⁻¹).support := by rw [hs]; simp
  have hx : (p⁻¹) 0 ≠ 0 := Equiv.Perm.mem_support.mp hxmem
  have hnon : (p⁻¹).toList 0 ≠ [] := by
    intro h
    exact (Equiv.Perm.toList_eq_nil_iff.mp h) hxmem
  obtain ⟨a, rest, he⟩ := List.exists_cons_of_ne_nil hnon
  have ha : a=(0 : Fin n) := by
    have hh := Equiv.Perm.toList_getElem_zero (p⁻¹) 0 hxmem
    simpa only [he, List.getElem_cons_zero] using hh
  subst a
  have hchain : Follows p ((p⁻¹).toList 0) := by
    apply (follows_iff_isChain _ _).mpr
    apply List.isChain_iff_getElem.mpr
    intro i hi
    simp only [Equiv.Perm.getElem_toList, pow_succ', Equiv.Perm.mul_apply]
  have hform : ((0 : Fin n)::rest).formPerm=(p⁻¹) := by
    rw [← he, Equiv.Perm.formPerm_toList]
    exact @Equiv.Perm.IsCycle.cycleOf_eq (Fin n) (p⁻¹) 0
      (Equiv.Perm.instDecidableRelSameCycle (p⁻¹)) hc hx
  refine ⟨rest, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using Equiv.Perm.nodup_toList (p⁻¹) (0 : Fin n)
  · intro i
    rw [← he]
    apply Equiv.Perm.mem_toList_iff.mpr
    have himem : i ∈ (p⁻¹).support := by rw [hs]; simp
    exact ⟨hc.sameCycle hx (Equiv.Perm.mem_support.mp himem), hxmem⟩
  · simpa only [he] using hchain
  · rw [← hform]
    exact List.formPerm_apply_getLast _ _

/-- For every balanced lift whose target is a single full-support cycle, construct
an actual closed integer-cursor word with the exact claimed rotation count. -/
theorem cyclic_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hp : p.IsCycle) (hs : p.support=Finset.univ) :
    ∃ w : List Letter,
      eval w = p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i = (i : ℤ)+d i) ∧
      (rotations w : ℤ) = (∑ i : Fin n, |d i|) -
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) ∧
      w.length=2*rotations w+n-1 := by
  have hsinv : (p⁻¹).support=Finset.univ := by
    rw [Equiv.Perm.support_inv, hs]
  obtain ⟨rest, hnd, hcover, hfollow, hlast⟩ := exists_complete_cycle_order hp.inv hsinv
  exact full_cycle_service hn hd rest hnd hcover hfollow hlast

#print axioms exists_complete_cycle_order
#print axioms cyclic_service
end LRX.BufferProgram
