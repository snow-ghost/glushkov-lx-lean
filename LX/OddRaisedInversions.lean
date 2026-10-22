import LX.OddMiddleInversions
import LX.SingleRaisePrice

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem inversions_add_constant (d : Fin n → ℤ) (t : ℤ) :
    inversions (fun i => d i+t)=inversions d := by
  unfold inversions LRX.LiftedModel.inversionCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : targets (fun i => d i+t) j-targets (fun i => d i+t) i=targets d j-targets d i := by
    unfold targets
    ring
  rw [he]

end LX.AffineScan

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A balanced single-coordinate raise supplies its balanced uniformly
shifted source. Both boards keep the actual target permutation. -/
theorem raised_source_lift {p : State n} {c : Fin n} {e : Fin n → ℤ} (a : Fin n)
    (hd : IsLift p (c : ℤ) (raiseAt e a)) :
    IsLift p ((c : ℤ)+1) (fun i => e i+1) := by
  refine ⟨?_,?_⟩
  · have hs : (∑ i : Fin n,raiseAt e a i)=(∑ i : Fin n,e i)+(n : ℤ) := by
      simp [raiseAt,Finset.sum_add_distrib]
    have hz := hd.1
    rw [hs] at hz
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one] using hz
  · intro i
    have hh := lift_residue hd i
    have he : (raiseAt e a i : Fin n)=(e i : Fin n) := by simp [raiseAt]
    rw [he] at hh
    apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self] at hh ⊢
    linear_combination hh

theorem raise_source_eq (e : Fin n → ℤ) (a : Fin n) :
    raiseMinimum (fun i => e i+1) a=raiseAt e a := by
  funext i
  rw [raise_minimum_apply]
  simp only [raiseAt,Nat.cast_ite,Nat.cast_zero]
  ring

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_raised_base_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    inversions (oddBase m hm hn c)+2 ≤ inversions (raiseAt (oddBase m hm hn c) a) := by
  have hsource := raised_source_lift a hd
  have hw : ∀ i j : Fin n,(oddBase m hm hn c i+1)-(oddBase m hm hn c j+1) < (n : ℤ) := by
    intro i j
    have hi := odd_base_bounds m hm hn c i
    have hj := odd_base_bounds m hm hn c j
    omega
  have hlo : ∀ i : Fin n,-((m-1 : ℕ) : ℤ) ≤ oddBase m hm hn c i+1 := by
    intro i
    have hh := odd_base_bounds m hm hn c i
    omega
  have hh := raise_coordinate_inversions_lower hsource a hw (m-1) hlo
  rw [raise_source_eq,inversions_add_constant] at hh
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hgoal : (inversions (oddBase m hm hn c) : ℤ)+2 ≤
      inversions (raiseAt (oddBase m hm hn c) a) := by omega
  exact_mod_cast hgoal

theorem odd_middle_raised_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    m*(m-1)+1+2*((m-c.val+1)/2)+2 ≤ inversions (raiseAt (oddBase m hm hn c) a) := by
  have hbase := odd_middle_base_inversions m hm hn c hc hcl
  have hraise := odd_raised_base_inversions m hm hn c a hd
  omega

#print axioms odd_raised_base_inversions
#print axioms odd_middle_raised_inversions
end LX.Antipode
