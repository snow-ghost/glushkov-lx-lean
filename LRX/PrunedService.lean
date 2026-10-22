import LRX.PrunedReachability
import LRX.AffineReducedPrice

/-! The retained part of a root star has a literal service and exact price.
Only geometric star coverage, cycle invariance, and retained balance are inputs. -/
namespace LRX.PrunedLift
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem pruned_service_price (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : (p⁻¹) 0 ≠ 0)
    (hstar : RootStar p d 0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S)
    (hbalance : ∑ i ∈ S, d i=0) :
    ∃ w : List Letter,
      eval w=permutation p S hS ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i=
        (i : ℤ)+displacement S d i) ∧
      BufferProgram.exchanges w=LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+displacement S d i) ∧
      (w.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+displacement S d i) : ℤ)+
        (∑ i : Fin n, |displacement S d i|)-
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ)
          ((i : ℤ)+displacement S d i) := by
  have hs := is_lift hd S hS hbalance
  have hr : ((permutation p S hS)⁻¹) 0 ≠ 0 := by
    simpa only [Equiv.Perm.inv_def, permutation_symm_apply, ite_eq_left hkeep] using hroot
  have hstar' := root_star_pruned p d 0 hstar S hS hkeep
  exact BufferProgram.reachable_service_price hn hs hr
    (fun i hi => root_star_reaches _ _ _ hstar' i hi)

omit [NeZero n] in
theorem sum_inverse (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (f : Fin n → ℤ) :
    (∑ i ∈ S, f (p.symm i))=∑ i ∈ S, f i := by
  apply Finset.sum_bij (fun i _ => p.symm i)
  · intro i hi
    exact (inverse_mem_iff p S hS i).mpr hi
  · intro i hi j hj he
    exact p.symm.injective he
  · intro j hj
    exact ⟨p j, (hS j).mpr hj, p.symm_apply_apply j⟩
  · intro i hi
    rfl

omit [NeZero n] in
theorem canonical_balance (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) :
    (∑ i ∈ S, ((p.symm i : ℤ)-(i : ℤ)))=0 := by
  rw [Finset.sum_sub_distrib, sum_inverse p S hS (fun i => (i : ℤ)), sub_self]

#print axioms pruned_service_price
#print axioms canonical_balance
end LRX.PrunedLift
