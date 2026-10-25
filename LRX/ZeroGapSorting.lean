import LRX.ZeroGapDescent
import Mathlib

/-! Termination of the zero-gap sorting process and its exact number of
endpoint transpositions. Recentring is part of the mathematical trace. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def mass (d : Fin n → ℤ) : ℕ := ∑ i, (d i).natAbs

theorem mass_cast (d : Fin n → ℤ) : (mass d : ℤ)=∑ i : Fin n, |d i| := by
  simp only [mass,Nat.cast_sum,Int.natCast_natAbs]

inductive SortingTrace : State n → (Fin n → ℤ) → ℕ → Prop
  | done {p d} (hz : ∀ i, d i=0) : SortingTrace p d 0
  | step {p d} (u v : Fin n) (hv : 0 < v.val)
      (hpos : 0 < RotationWords.localDisplacement d u 0)
      (hneg : RotationWords.localDisplacement d u v < 0)
      (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → RotationWords.localDisplacement d u i=0)
      {M : ℕ}
      (tail : SortingTrace (Equiv.swap 0 v*RotationWords.localTarget p 0 u)
        (exchange (RotationWords.localDisplacement d u) v) M) : SortingTrace p d (M+1)

theorem identity_inversions : LiftedModel.inversionCount (fun i : Fin n => (i : ℤ))=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change (if i < j then (((j : ℤ)-(i : ℤ))/(n : ℤ)).natAbs else 0)=0
  by_cases hij : i < j
  · rw [ite_eq_left hij]
    apply nonnegative_quotient_term
    · have h : (i : ℤ) < j := by exact_mod_cast hij
      omega
    · have hi : (0 : ℤ) ≤ i := by positivity
      have hj : (j : ℤ) < n := by exact_mod_cast j.isLt
      omega
  · rw [ite_eq_right hij]

theorem exists_sorting_trace {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ M : ℕ, SortingTrace p d M ∧
      (∑ i : Fin n, |d i|)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+M := by
  have main : ∀ m : ℕ, ∀ p : State n, ∀ d : Fin n → ℤ, mass d=m →
      AffineLift.IsLift p 0 d → (∀ i, 2*|d i| < (n : ℤ)) →
      ∃ M : ℕ, SortingTrace p d M ∧
        (∑ i : Fin n, |d i|)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+M := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p d hmass hd hs
      by_cases hne : ∃ i, d i ≠ 0
      · obtain ⟨u,v,hv,hpos,hneg,hgap,hd',hs',hm,hC⟩ := exists_descent hd hs hne
        have hsmaller : mass (exchange (RotationWords.localDisplacement d u) v) < m := by
          have h0 := mass_cast d
          have h1 := mass_cast (exchange (RotationWords.localDisplacement d u) v)
          rw [hmass] at h0
          omega
        obtain ⟨M,htrace,hcount⟩ := ih _ hsmaller _ _ rfl hd' hs'
        refine ⟨M+1,SortingTrace.step u v hv hpos hneg hgap htrace,?_⟩
        have hC' := congrArg (fun k : ℕ => (k : ℤ)) hC
        push_cast at hC'
        omega
      · have hz : ∀ i, d i=0 := by intro i; by_contra h; exact hne ⟨i,h⟩
        refine ⟨0,SortingTrace.done hz,?_⟩
        simp only [hz,abs_zero,Finset.sum_const_zero,add_zero,identity_inversions,Nat.cast_zero]
  exact main (mass d) p d rfl hd hshort


#print axioms exists_sorting_trace
end LRX.ZeroGap
