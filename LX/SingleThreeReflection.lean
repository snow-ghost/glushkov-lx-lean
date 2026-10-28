import LX.SingleThreeGeometry
import Mathlib

namespace LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Splitting the consecutive positive triple preserves displacement mass
and adds one finite inversion. -/
theorem consecutive_three_swap_mass (q : State n) (a b c : Fin n)
    (hab : a.val+1=b.val) (hbc : b.val+1=c.val) (ha : q a=b) (hb : q b=c) :
    (∑ i, |displacement (q*Equiv.swap a b) i|)=∑ i, |displacement q i| := by
  have hne : a ≠ b := by intro h; have := congrArg Fin.val h; omega
  have hterm (i : Fin n) : |displacement (q*Equiv.swap a b) i|=
      |displacement q i|+(if i=a then (1 : ℤ) else 0)-(if i=b then 1 else 0) := by
    by_cases hia : i=a
    · subst i
      simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_left,ha,hb,
        ite_true,ite_eq_right hne,abs_eq_max_neg]
      omega
    · by_cases hib : i=b
      · subst i
        simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_right,ha,hb,
          ite_true,ite_eq_right hia,abs_eq_max_neg]
        omega
      · simp only [displacement,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hia hib,
          ite_eq_right hia,ite_eq_right hib,add_zero,sub_zero]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib,Finset.sum_sub_distrib]

/-- Splitting the consecutive 3-cycle yields an actual noncrossing matching
with two fixed positions. The existing matching classification identifies
the entire input as a reflection with one neighboring swap. -/
theorem single_three_neighbor_reflection_at_zero (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1) (hzero : q 0=0)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∃ a b : Fin n,a.val+1=b.val ∧ ∀ i : Fin n,(q*Equiv.swap a b) i= -i := by
  classical
  obtain ⟨a,b,c,hab,hbc,ha,hb,hc,houtside⟩ := single_three_consecutive_at_zero q hq he hfixed hback
  have habn : a ≠ b := by intro h; have := congrArg Fin.val h; omega
  have hacn : a ≠ c := by intro h; have := congrArg Fin.val h; omega
  have hbcn : b ≠ c := by intro h; have := congrArg Fin.val h; omega
  have ha0 : a ≠ 0 := by
    intro h
    have ha' := ha
    rw [h,hzero] at ha'
    have := congrArg Fin.val ha'
    have := congrArg Fin.val h
    omega
  have hb0 : b ≠ 0 := by
    intro h
    rw [h,Fin.val_zero] at hab
    omega
  let Q := q*Equiv.swap a b
  have hQa : Q a=c := by simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_left,hb]
  have hQb : Q b=b := by simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_right,ha]
  have hQi (i : Fin n) (hia : i ≠ a) (hib : i ≠ b) : Q i=q i := by
    simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hia hib]
  have hQc : Q c=a := (hQi c hacn.symm hbcn.symm).trans hc
  have himage (i : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c) :
      q i ≠ a ∧ q i ≠ b ∧ q i ≠ c := by
    exact ⟨fun h => hic (q.injective (h.trans hc.symm)),
      fun h => hia (q.injective (h.trans ha.symm)),
      fun h => hib (q.injective (h.trans hb.symm))⟩
  have hinv : Function.Involutive Q := by
    intro i
    by_cases hia : i=a
    · subst i; rw [hQa,hQc]
    by_cases hib : i=b
    · subst i; rw [hQb,hQb]
    by_cases hic : i=c
    · subst i; rw [hQc,hQa]
    have hi := himage i hia hib hic
    rw [hQi i hia hib,hQi (q i) hi.1 hi.2.1]
    exact houtside i hia hib hic
  have hfOld : fixedPositions q={0} := by
    ext i
    simp only [mem_fixedPositions,Finset.mem_singleton]
    exact ⟨hfixed i,fun h => by rw [h,hzero]⟩
  have hfNew : fixedPositions Q={0,b} := by
    ext i
    simp only [mem_fixedPositions,Finset.mem_insert,Finset.mem_singleton]
    by_cases hia : i=a
    · subst i
      simp [hQa,hacn.symm,ha0,habn]
    by_cases hib : i=b
    · subst i
      simp [hQb]
    rw [hQi i hia hib]
    constructor
    · intro hi
      exact Or.inl (hfixed i hi)
    · rintro (hi | hi)
      · rw [hi,hzero]
      · exact False.elim (hib hi)
  have hfc : (fixedPositions Q).card=2 := by rw [hfNew]; simp [hb0.symm]
  have hsOld := fixed_positions_card q
  rw [hfOld] at hsOld
  simp only [Finset.card_singleton,Nat.cast_one] at hsOld
  have hsNew := fixed_positions_card Q
  rw [hfc] at hsNew
  have hs : Q.support.card=2*q.cycleFactorsFinset.card := by omega
  have hmass := consecutive_three_swap_mass q a b c hab hbc ha hb
  have hI := adjacent_raising_inversion_price q a b hab.symm (by rw [ha,hb]; omega)
  have hdef : (∑ i, |displacement Q i|)-(inversionNumber Q : ℤ)=
      (q.cycleFactorsFinset.card : ℤ) := by
    change (∑ i, |displacement (q*Equiv.swap a b) i|)-(inversionNumber (q*Equiv.swap a b) : ℤ)=_
    rw [hmass,hI]
    unfold cycleDefect at hq
    rw [he] at hq
    push_cast at *
    omega
  have hnc : NoncrossingPairs Q := finite_shallow_matching_noncrossing Q _ hs hdef
  have hQzero : Q 0=0 := (hQi 0 ha0.symm hb0.symm).trans hzero
  have hnoadj (i : Fin n) : i.val+1 ≠ (Q i).val := by
    intro hi
    by_cases hia : i=a
    · subst i; rw [hQa] at hi; omega
    by_cases hib : i=b
    · subst i; rw [hQb] at hi; omega
    by_cases hic : i=c
    · subst i; rw [hQc] at hi; omega
    rw [hQi i hia hib] at hi
    exact hback i (q i) hi (houtside i hia hib hic)
  exact ⟨a,b,hab,fixed_count_two_reflection Q hinv hnc hQzero hfc hnoadj⟩

#print axioms single_three_neighbor_reflection_at_zero
end LX.CycleGeometry
