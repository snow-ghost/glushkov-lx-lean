import LRX.WindowReplacementRank
import LRX.ReducedServiceRoute

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ}

theorem swap_displacement_mass (a b : Fin n) (hab : a.val < b.val) :
    (∑ i : Fin n, |displacement (Equiv.swap a b) i|)=2*((b : ℤ)-(a : ℤ)) := by
  classical
  have hne : a ≠ b := by intro h; subst b; omega
  have hs : (∑ i ∈ ({a,b} : Finset (Fin n)), |displacement (Equiv.swap a b) i|)=
      ∑ i : Fin n, |displacement (Equiv.swap a b) i| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hout
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hout
    simp [displacement,Equiv.swap_apply_of_ne_of_ne hout.1 hout.2]
  rw [← hs,Finset.sum_pair hne]
  simp only [displacement,Equiv.swap_apply_left,Equiv.swap_apply_right]
  rw [abs_of_nonneg (by omega),abs_of_nonpos (by omega)]
  ring

theorem swap_half_load_between (a b : Fin n) (hab : a.val < b.val) (e : ℕ)
    (hae : a.val < e) (heb : e ≤ b.val) : halfLoad (Equiv.swap a b) e=1 := by
  have hf : forward (Equiv.swap a b) e={a} := by
    ext i
    simp only [mem_forward,Finset.mem_singleton]
    by_cases hia : i=a
    · subst i
      simp [Equiv.swap_apply_left,hae,heb]
    · by_cases hib : i=b
      · subst i
        simp only [Equiv.swap_apply_right]
        constructor
        · intro h; omega
        · intro h; exact False.elim (hia h)
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
        constructor
        · intro h; omega
        · intro h; exact False.elim (hia h)
  simp [halfLoad,hf]

/-- Exact pair service at its left endpoint, with canonical integer positions and known rotations. -/
theorem pair_left_exact_service [NeZero n] (hn : 2 ≤ n) (a b : Fin n) (hab : a.val < b.val) :
    ∃ s : ExactService n, s.service.port=a ∧ s.service.target=Equiv.swap a b ∧
      s.displacement=displacement (Equiv.swap a b) ∧
      (BufferProgram.rotations s.service.word : ℤ)=2*((b : ℤ)-(a : ℤ))-2 := by
  have hne : a ≠ b := by intro h; subst b; omega
  have hd : AffineLift.IsLift (Equiv.swap a b) 0 (displacement (Equiv.swap a b)) := by
    simpa using canonical_lift (Equiv.swap a b)
  have hroot : displacement (Equiv.swap a b) a ≠ 0 := by
    simp only [displacement,Equiv.swap_apply_left]
    omega
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := single_cycle_exact_service hn (Equiv.Perm.isCycle_swap hne)
    hd (displacement_short _) a hroot
  rw [swap_displacement_mass a b hab,port_load_eq_twice_half,
    swap_half_load_between a b hab (a.val+1) (by omega) (by omega)] at hrot
  exact ⟨s,hport,htarget,hdisp,by simpa using hrot⟩

#print axioms pair_left_exact_service
end LRX.FiniteCuts
