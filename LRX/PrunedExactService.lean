import LRX.FiniteRootStar
import LRX.ReducedServiceRoute

/-! Pruned root stars provide exact closed services suitable for composition
with the separately served cycles. Canonical finite roots need no balance premise. -/
namespace LRX.PrunedLift
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem exists_pruned_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : RootStar p d 0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S)
    (hbalance : ∑ i ∈ S, d i=0) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad (displacement S d) 0 := by
  have hs := is_lift hd S hS hbalance
  have hr : displacement S d 0 ≠ 0 := by simpa [displacement,hkeep] using hroot
  have hstar' := root_star_pruned p d 0 hstar S hS hkeep
  apply exists_exact_service hn 0 hs (short hshort S) hr
  intro i hi
  have he : localTarget (permutation p S hS) 0 0=permutation p S hS := by simp [localTarget]
  have hd' : localDisplacement (displacement S d) 0=displacement S d := by
    funext j
    simp [localDisplacement]
  rw [he, hd']
  exact root_star_reaches _ _ _ hstar' i (by simpa only [hd'] using hi)

theorem enclosing_pruned_exact_service (hn : 2 ≤ n) (p : State n)
    (hroot : (p⁻¹) 0 ≠ 0) (u v : Fin n)
    (hu : (p⁻¹).SameCycle 0 u) (hv : (p⁻¹).SameCycle 0 v)
    (hinside : ∀ i, (p⁻¹) i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S (fun i => (p.symm i : ℤ)-(i : ℤ)) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S (fun j => (p.symm j : ℤ)-(j : ℤ)) i|)-
          portLoad (displacement S (fun i => (p.symm i : ℤ)-(i : ℤ))) 0 := by
  have hs (i : Fin n) : |(p.symm i : ℤ)-(i : ℤ)| < (n : ℤ) := by
    have hi := i.isLt
    have hp := (p.symm i).isLt
    rw [abs_lt]
    omega
  have hr : (p.symm (0 : Fin n) : ℤ)-(0 : Fin n) ≠ 0 := by
    intro h
    apply hroot
    change p.symm 0=0
    apply Fin.ext
    exact_mod_cast (sub_eq_zero.mp h)
  exact exists_pruned_exact_service hn (AffineLift.canonical_lift p) hs hr
    (enclosing_cycle_root_star p 0 u v hu hv hinside) S hS hkeep (canonical_balance p S hS)

#print axioms exists_pruned_exact_service
#print axioms enclosing_pruned_exact_service
end LRX.PrunedLift
