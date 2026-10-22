import LX.InvariantCycleGap
import Mathlib.Data.Fin.Parity

namespace LX.CycleGeometry
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Even displacement is preserved along every actual cycle, expressed
inside the cyclic additive group so that the seam is handled as well. -/
theorem same_cycle_even_difference (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : q.SameCycle i j) : Even (j-i) := by
  obtain ⟨k,hk⟩ := hij.exists_nat_pow_eq
  have hp : ∀ k : ℕ,Even ((q^k) i-i) := by
    intro k
    induction k with
    | zero => simpa using (even_zero : Even (0 : Fin n))
    | succ k ih =>
      have hs := (he ((q^k) i)).add ih
      simpa only [pow_succ',Equiv.Perm.mul_apply,sub_add_sub_cancel] using hs
  rw [← hk]
  exact hp k

/-- In even dimension, a cycle whose displacements are even cannot
contain two linearly neighboring physical positions. -/
theorem even_displacement_no_neighbor_cycle (hn2 : 2 ≤ n) (hn : Even n)
    (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : i.val+1=j.val) : ¬q.SameCycle i j := by
  intro hs
  have hd := same_cycle_even_difference q he i j hs
  have hj : i+1=j := LX.MatchingGeometry.eq_add_of_value_add i j 1 hij
  rw [← hj] at hd
  have hdiff : i+1-i=(1 : Fin n) := by ring
  rw [hdiff] at hd
  have hm := (Fin.even_iff_mod_of_even hn).mp hd
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < n)] at hm

end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The entire even unit-reserve branch is paid. The hypothetical unpaid
input would have even displacements and two fixed points; its actual
zero-defect cycle gaps then force every cycle to be a pair, contradicting
the unit-reserve rank equation. -/
theorem even_unit_reserve_upper_word {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  classical
  by_contra hunpaid
  let q := permutation p a
  let Q := shiftConjugate q a.val
  have hf := even_unit_unpaid_all_minima_two_fixed hn4 m hn ha hunit hunpaid a ha
  have hp := even_unit_unpaid_offsets_even hn4 m hn ha hunit hunpaid a ha
  obtain ⟨hz,_,_,hexcess⟩ := even_unit_reserve_source m hn ha hunit
  rw [hf] at hexcess
  have he (i : Fin n) : Even (q i-i) := by
    have hh : Even (cyclicOffset p a i) := Fin.even_of_val (Nat.even_iff.mpr (hp i))
    rwa [cyclic_offset_normalized] at hh
  have hQeven (i : Fin n) : Even (Q i-i) := by
    have hh := he (i+a)
    have hdiff : Q i-i=q (i+a)-(i+a) := by
      dsimp only [Q]
      rw [shift_conjugate_apply]
      ring
    rwa [hdiff]
  have hQzero : cycleDefect Q=0 := by
    dsimp only [Q]
    rw [LX.CycleGeometry.shift_cycle_defect]
    exact hz
  have hQ0 : Q 0=0 := by
    simp only [Q,q,shift_conjugate_apply,zero_add,permutation_anchor,sub_self]
  obtain ⟨hs,hc⟩ := LX.CycleGeometry.shift_support_and_cycle_count q a.val
  have hfQ : (fixedPositions Q).card ≤ 2 := by
    have h1 := fixed_positions_card q
    have h2 := fixed_positions_card Q
    change (fixedPositions q).card=2 at hf
    rw [hf] at h1
    have hs' : Q.support.card=q.support.card := hs
    omega
  have hnEven : Even n := ⟨m,by omega⟩
  have hpairs := LX.CycleGeometry.two_fixed_no_neighbor_cycles_are_pairs Q hQzero hQ0 hfQ
    (LX.CycleGeometry.even_displacement_no_neighbor_cycle (by omega) hnEven Q hQeven)
  have hsupport : Q.support.card=2*Q.cycleFactorsFinset.card := by
    rw [← cycle_support_card_sum Q]
    calc
      _ = ∑ _g ∈ Q.cycleFactorsFinset,2 := Finset.sum_congr rfl hpairs
      _ = _ := by simp [mul_comm]
  change Q.support.card=q.support.card at hs
  change Q.cycleFactorsFinset.card=q.cycleFactorsFinset.card at hc
  rw [hs,hc] at hsupport
  change q.support.card=2*q.cycleFactorsFinset.card+2 at hexcess
  omega

/-- Both zero and unit dimension-wide reserve are now paid in even size. -/
theorem even_unpaid_reserve_at_least_two {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    2 ≤ (m : ℤ)*(m-1)-inversions (displacement p a) := by
  have hpos := unpaid_positive_exchange_reserve hn4 ha hunpaid
  have hdiv : n/2=m := by omega
  rw [hdiv] at hpos
  have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
  have hpos' : (inversions (displacement p a) : ℤ)<(m : ℤ)*(m-1) := by nlinarith
  by_contra hnot
  have heq : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1) := by omega
  exact hunpaid (even_unit_reserve_upper_word hn4 m hn ha heq)

#print axioms even_unit_reserve_upper_word
#print axioms even_unpaid_reserve_at_least_two
end LX.AnchoredPhases
