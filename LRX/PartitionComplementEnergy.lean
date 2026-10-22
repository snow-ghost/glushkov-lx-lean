import LRX.PacketGapAggregate

/-! The packet complement-energy estimate applies to every interval in the
actual partition, without changing physical distances or choosing a new root. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def complementCoordinate (S : Finset (Fin n)) (a i : Fin n) : ℤ :=
  (i : ℤ)-(next S a : ℤ)+if i.val ≤ a.val then (n : ℤ) else 0

theorem complement_injective (S : Finset (Fin n)) (a : Fin n) :
    Function.Injective (complementCoordinate S a) := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  unfold complementCoordinate at he
  by_cases hia : i.val ≤ a.val <;> by_cases hja : j.val ≤ a.val
  · simp only [ite_eq_left hia,ite_eq_left hja] at he
    apply Fin.ext
    omega
  · simp only [ite_eq_left hia,ite_eq_right hja,add_zero] at he
    omega
  · simp only [ite_eq_right hia,ite_eq_left hja,add_zero] at he
    omega
  · simp only [ite_eq_right hia,ite_eq_right hja,add_zero] at he
    apply Fin.ext
    omega

theorem complement_bounds (S : Finset (Fin n)) (a i : Fin n) (hi : i ∈ S) :
    0 ≤ complementCoordinate S a i ∧ complementCoordinate S a i < (n-size S a : ℕ) := by
  have hn := next_le S a
  have ha := lt_next S a
  have hin := i.isLt
  unfold complementCoordinate size
  by_cases hia : i.val ≤ a.val
  · simp only [ite_eq_left hia]
    omega
  · have hnext := next_le_member S a i hi (by omega)
    simp only [ite_eq_right hia,add_zero]
    omega

theorem complement_residue (S : Finset (Fin n)) (a i : Fin n) :
    ((complementCoordinate S a i : ℤ) : Fin n)=i-(next S a : Fin n) := by
  unfold complementCoordinate
  split_ifs <;> simp

theorem arrow_le_complement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (S : Finset (Fin n)) (a i : Fin n) :
    |d i| ≤ |complementCoordinate S a (p.symm i)-complementCoordinate S a i| := by
  apply PrunedLift.shortest_representative
    (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) (FiniteWindow.majorized_short hd hm i)
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  rw [Int.cast_sub,complement_residue,complement_residue]
  have h := AffineLift.lift_residue hd i
  linear_combination h

theorem core_complement_energy {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (a : Fin n) :
    PrunedLift.coreEnergy p d ≤ 2*(PrunedLift.coreHalfSize p d : ℤ)*
      ((n : ℤ)-size (PrunedLift.core p d 0) a-PrunedLift.coreHalfSize p d) := by
  classical
  let S := PrunedLift.core p d 0
  let f := complementCoordinate S a
  have hf := complement_injective S a
  have hb := complement_bounds S a
  have hinv := PrunedLift.core_invariant p d 0
  have hb' : ∀ i ∈ S, 0 ≤ f (p.symm i) ∧ f (p.symm i) < (n-size S a : ℕ) := by
    intro i hi
    exact hb _ ((PrunedLift.inverse_mem_iff p S hinv i).mpr hi)
  have hcard := FiniteCoordinates.card_le_of_coordinates S f (n-size S a) hf.injOn
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  have hbalance : (∑ i ∈ S, (f (p.symm i)-f i))=0 := by
    rw [Finset.sum_sub_distrib,PrunedLift.sum_inverse p S hinv,sub_self]
  have hcap := FiniteCoordinates.energy_capacity S f (fun i => f (p.symm i)) (n-size S a)
    hf.injOn (hf.comp p.symm.injective).injOn
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
    (fun i hi => (hb' i hi).1) (fun i hi => (hb' i hi).2) hbalance hcard
  have hmass : (∑ i ∈ S, |d i|) ≤ ∑ i ∈ S, |f (p.symm i)-f i| :=
    Finset.sum_le_sum (fun i _ => arrow_le_complement hd hm S a i)
  have hsize : size S a ≤ n := by have := next_le S a; unfold size; omega
  rw [Nat.cast_sub hsize] at hcap
  exact hmass.trans hcap

theorem core_reserve_complement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (a : Fin n) :
    (PrunedLift.coreHalfSize p d : ℤ)*(2*(size (PrunedLift.core p d 0) a : ℤ)-n+PrunedLift.coreHalfSize p d) ≤
      PrunedLift.coreReserve p d := by
  have h := core_complement_energy hd hm a
  unfold PrunedLift.coreReserve
  nlinarith

#print axioms core_complement_energy
#print axioms core_reserve_complement
end LRX.FiniteGaps
