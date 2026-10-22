import LRX.ContractionStructure
import LRX.ShallowCutShift

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem displacement_mass_inverse (p : State n) :
    (∑ i : Fin n, |displacement p.symm i|)=∑ i : Fin n, |displacement p i| := by
  have h := Equiv.sum_comp p (fun i : Fin n => |displacement p.symm i|)
  simpa only [displacement,Equiv.symm_apply_apply,abs_sub_comm] using h.symm

theorem shallow_iff_direct [NeZero n] (p : State n) : Shallow p ↔
    (∑ i : Fin n, |displacement p i|)-(inversionNumber p : ℤ)=(p.support.card : ℤ)-1 := by
  unfold Shallow
  rw [displacement_mass_inverse,canonical_inversion_count]
  change _ ↔ _
  have hI : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hI]
  omega

/-- Contracting a neighboring arrow of a cycle with at least three moving
vertices produces a shallow cycle again. Both arrow directions are covered. -/
theorem contract_shallow_cycle {p : State (n+1)} (hp : p.IsCycle)
    (hc : 3 ≤ p.support.card) (hs : Shallow p) (a : Fin (n+1))
    (hadj : |displacement p a|=1) : (contract p a).IsCycle ∧ Shallow (contract p a) := by
  classical
  have hn : 0 < n := by
    have hle : p.support.card ≤ n+1 := by simpa using Finset.card_le_univ p.support
    omega
  letI : NeZero n := ⟨by omega⟩
  refine ⟨contract_cycle hp hc a hadj,?_⟩
  apply (shallow_iff_direct _).mpr
  have hE := contraction_energy_minus_inversions p a (by rw [hadj])
  rw [hadj] at hE
  have hS := (shallow_iff_direct p).mp hs
  have hcard := congrArg (fun k : ℕ => (k : ℤ)) (contract_cycle_support_card hp hc a hadj)
  push_cast at hcard
  linarith only [hE,hS,hcard]

theorem contract_fixed_extension (p : State (n+1)) (a : Fin (n+1)) (ha : p a=a) :
    (contract p a).extendDomain (finSuccAboveEquiv a)=p := by
  apply Equiv.ext
  intro j
  by_cases hj : j=a
  · subst j
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp),ha]
  · obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hj
    subst j
    have he := Equiv.Perm.extendDomain_apply_image (contract p a) (finSuccAboveEquiv a) i
    change ((contract p a).extendDomain (finSuccAboveEquiv a)) (a.succAbove i)=
      a.succAbove (contract p a i) at he
    rw [he]
    have hc := contract_entry p a i
    rwa [ha] at hc

/-- Removing a fixed position preserves the canonical shallow cycle and
its moving support size; this is the elementary rank-compression step. -/
theorem contract_fixed_shallow_cycle {p : State (n+1)} (hp : p.IsCycle) (hs : Shallow p)
    (a : Fin (n+1)) (ha : p a=a) :
    (contract p a).IsCycle ∧ Shallow (contract p a) ∧ (contract p a).support.card=p.support.card := by
  classical
  have hn : 0 < n := by
    have hle : p.support.card ≤ n+1 := by simpa using Finset.card_le_univ p.support
    have hc := hp.two_le_card_support
    omega
  letI : NeZero n := ⟨by omega⟩
  have hext := contract_fixed_extension p a ha
  have hcard := Equiv.Perm.card_support_extend_domain (finSuccAboveEquiv a) (g := contract p a)
  rw [hext] at hcard
  have hzero : displacement p a=0 := by simp [displacement,ha]
  refine ⟨cycle_of_puncture_extension _ a (by rwa [hext]),?_,hcard.symm⟩
  apply (shallow_iff_direct _).mpr
  have hE := contraction_energy_minus_inversions p a (by simp [hzero])
  rw [hzero,abs_zero,sub_zero] at hE
  have hS := (shallow_iff_direct p).mp hs
  rw [hcard] at hS
  linarith only [hE,hS]

#print axioms contract_shallow_cycle
#print axioms contract_fixed_shallow_cycle
end LRX.FiniteCuts
