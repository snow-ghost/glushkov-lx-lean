import LX.AnchorReserveRigidity
import LX.FixedPairJoinPrice
import LX.JoinMinimumPair
import LX.OddUnitFixedNeighbors
import LX.ZeroExchangeReserve
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem joined_source_permutation (p : State n) (a u : Fin n) :
    LX.Core.FiniteCuts.shiftedLiftPermutation (p*Equiv.swap u (u+1)).symm
      (phase p a-1) ((height p a : ℤ)+1)=permutation p a*Equiv.swap u (u+1) := by
  apply Equiv.ext
  intro i
  change p (Equiv.swap u (u+1) i)+(((phase p a-1)+((height p a : ℤ)+1) : ℤ) : Fin n)=
    p (Equiv.swap u (u+1) i)+(a-p a)
  congr 1
  simp only [phase,Int.cast_add,Int.cast_sub,Int.cast_natCast,Int.cast_one,Fin.cast_val_eq_self]
  ring

/-- Joining the neighboring fixed points produces a majorized lift at the
full dimension-wide capacity. The existing LX.Core equality classification then
identifies the changed input as a circular reflection. -/
theorem odd_zero_strip_join_reflection (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hm : Majorized (displacement p a))
    (hzero : anchorReserve p a=0) (u : Fin n)
    (hu : permutation p a u=u) (hv : permutation p a (u+1)=u+1) :
    ∃ r : Fin n,∀ i,(p*Equiv.swap u (u+1)) i=r-i := by
  let h := height p a
  let d := displacement p a
  let e := joinMinima d u (u+1)
  let q := permutation p a
  have hd := is_lift p a
  have hne : u ≠ u+1 := LX.Core.LiftedModel.neighboring_positions_distinct (by omega) u
  have hdu : d u= -(h : ℤ) := by
    change displacement p a u= -(height p a : ℤ)
    rw [displacement_offset,cyclic_offset_normalized,hu,sub_self]
    simp
  have hdv : d (u+1)= -(h : ℤ) := by
    change displacement p a (u+1)= -(height p a : ℤ)
    rw [displacement_offset,cyclic_offset_normalized,hv,sub_self]
    simp
  have heLift : IsLift (p*Equiv.swap u (u+1)).symm (phase p a-1) e :=
    join_minima_lift hd u (u+1) hne rfl (hdu.trans hdv.symm)
  have heMajor : Majorized e := join_minima_majorized d u (u+1) hne hd.1 hm h hn hdu hdv
  have hn' : (n : ℤ)=2*(h : ℤ)+3 := by exact_mod_cast hn
  have heBand (i : Fin n) : 0 ≤ e i+((h : ℤ)+1) ∧ e i+((h : ℤ)+1)<(n : ℤ) := by
    have hh := short_coordinates heLift.1 heMajor i
    omega
  have hdef : LX.FiniteJoin.depthDeficit q=(h : ℤ) := by
    have hh := anchor_reserve_decomposition p a
    rw [hzero] at hh
    unfold LX.Core.FiniteCuts.cycleDefect at hh
    unfold LX.FiniteJoin.depthDeficit
    change (∑ i, |LX.Core.FiniteCuts.displacement q i|)-(LX.Core.FiniteCuts.inversionNumber q : ℤ)=(h : ℤ)
    change 0=(∑ i, |LX.Core.FiniteCuts.displacement q i|)-(LX.Core.FiniteCuts.inversionNumber q : ℤ)-
      (q.support.card : ℤ)+q.cycleFactorsFinset.card+q.support.card-q.cycleFactorsFinset.card-h at hh
    omega
  have hdefNew : LX.FiniteJoin.depthDeficit (q*Equiv.swap u (u+1))=(h : ℤ)+1 := by
    rw [LX.FiniteJoin.fixed_neighbor_deficit (by omega) q u hu hv,hdef]
  have hx := LX.Core.FiniteCuts.shifted_lift_inversion_formula heLift ((h : ℤ)+1) heBand
  rw [joined_source_permutation] at hx
  change (inversions e : ℤ)=((h : ℤ)+1)*((n : ℤ)-((h : ℤ)+1))+
    (LX.Core.FiniteCuts.inversionNumber (q*Equiv.swap u (u+1)) : ℤ)-
      2*LX.Core.FiniteCuts.leftDepth (q*Equiv.swap u (u+1)) at hx
  have hmass := LX.Core.FiniteCuts.displacement_mass_eq_twice_leftDepth (q*Equiv.swap u (u+1))
  unfold LX.FiniteJoin.depthDeficit at hdefNew
  have hfloor : n/2=h+1 := by omega
  have heq : (inversions e : ℤ)=((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
    rw [hfloor]
    push_cast
    nlinarith
  exact majorized_capacity_reflection heLift heMajor heq


#print axioms joined_source_permutation
#print axioms odd_zero_strip_join_reflection
end LX.AnchoredPhases
