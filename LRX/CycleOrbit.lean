import LRX.CyclicService

/-! Canonical finite orbit data for any target permutation, rather than only a
permutation consisting of one cycle. The orbit is invariant under the target. -/
namespace LRX.BufferProgram
variable {n : ℕ}

def orbitLabels (p : State n) (a : Fin n) : Finset (Fin n) :=
  ((p⁻¹).toList a).toFinset

theorem mem_orbitLabels (p : State n) (a i : Fin n) :
    i ∈ orbitLabels p a ↔ (p⁻¹).SameCycle a i ∧ (p⁻¹) a ≠ a := by
  simp only [orbitLabels, List.mem_toFinset, Equiv.Perm.mem_toList_iff,
    Equiv.Perm.mem_support]

theorem orbitLabels_invariant (p : State n) (a : Fin n) :
    (orbitLabels p a).image p.symm=orbitLabels p a := by
  have hs : (orbitLabels p a).image p.symm ⊆ orbitLabels p a := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [mem_orbitLabels] at hj ⊢
    exact ⟨hj.1.apply_right, hj.2⟩
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_image_of_injective _ p.symm.injective]

theorem exists_orbit_itinerary (p : State n) (a : Fin n) (ha : (p⁻¹) a ≠ a) :
    ∃ rest : List (Fin n), (p⁻¹).toList a=a::rest ∧ (a::rest).Nodup ∧
      (a::rest).toFinset=orbitLabels p a ∧ Follows p (a::rest) := by
  have hamem : a ∈ (p⁻¹).support := Equiv.Perm.mem_support.mpr ha
  have hnon : (p⁻¹).toList a ≠ [] := by
    intro h
    exact (Equiv.Perm.toList_eq_nil_iff.mp h) hamem
  obtain ⟨b, rest, he⟩ := List.exists_cons_of_ne_nil hnon
  have hb : b=a := by
    have hh := Equiv.Perm.toList_getElem_zero (p⁻¹) a hamem
    simpa only [he, List.getElem_cons_zero] using hh
  subst b
  refine ⟨rest, he, ?_, ?_, ?_⟩
  · simpa only [he] using Equiv.Perm.nodup_toList (p⁻¹) a
  · simp only [orbitLabels, he]
  · rw [← he]
    apply (follows_iff_isChain _ _).mpr
    apply List.isChain_iff_getElem.mpr
    intro i hi
    simp only [Equiv.Perm.getElem_toList, pow_succ', Equiv.Perm.mul_apply]

theorem invariant_sameCycle (p : State n) (S : Finset (Fin n))
    (hS : S.image p.symm=S) {a b : Fin n} (ha : a ∈ S)
    (hc : (p⁻¹).SameCycle a b) : b ∈ S := by
  obtain ⟨k, rfl⟩ := hc.exists_nat_pow_eq
  clear hc
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rw [← hS]
    exact Finset.mem_image.mpr ⟨_, ih, rfl⟩

theorem orbit_disjoint_of_not_mem (p : State n) (S : Finset (Fin n))
    (hS : S.image p.symm=S) (a : Fin n) (ha : a ∉ S) :
    Disjoint S (orbitLabels p a) := by
  apply Finset.disjoint_left.mpr
  intro i hi hio
  have hc := ((mem_orbitLabels p a i).mp hio).1
  exact ha (invariant_sameCycle p S hS hi hc.symm)

theorem mem_own_orbit (p : State n) (a : Fin n) (ha : (p⁻¹) a ≠ a) :
    a ∈ orbitLabels p a := (mem_orbitLabels p a a).mpr ⟨Equiv.Perm.SameCycle.refl _ _, ha⟩

theorem orbit_last_target (p : State n) (a : Fin n) (rest : List (Fin n))
    (he : (p⁻¹).toList a=a::rest) :
    (p⁻¹) ((a::rest).getLast (by simp))=a := by
  have hm : ((a::rest).getLast (by simp)) ∈ (p⁻¹).toList a := by
    rw [he]
    exact List.getLast_mem (by simp)
  have hnd : (a::rest).Nodup := by
    simpa only [he] using Equiv.Perm.nodup_toList (p⁻¹) a
  have h := Equiv.Perm.next_toList_eq_apply (p⁻¹) a _ hm
  simp only [he] at h
  rw [List.next_getLast_eq_head _ (by simp) hnd] at h
  exact h.symm

#print axioms orbitLabels_invariant
#print axioms exists_orbit_itinerary
end LRX.BufferProgram
