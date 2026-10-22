import LX.EvenUnitPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_unit_two_fixed_offsets_even {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hfixed : ∀ b : Fin n,GlobalMinimum p b → (fixedPositions (permutation p b)).card=2) :
    ∀ b : Fin n,GlobalMinimum p b → ∀ i : Fin n,(cyclicOffset p b i).val%2=0 := by
  have hunit_at (b : Fin n) (hb : GlobalMinimum p b) :
      (inversions (displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by
    have hx := Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
    rwa [hx]
  have main : ∀ r : ℕ,∀ b : Fin n,GlobalMinimum p b → ∀ i : Fin n,
      (cyclicOffset p b i).val=r → r%2=0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hb i hir
      have hh := (even_unit_reserve_height m hn hb (hunit_at b hb)).1
      have hno := two_fixed_no_offset_one p b (global_minimum_majorized hb)
        (by omega) (hfixed b hb) i
      by_cases hr : r < 2
      · have hz : r=0 := by omega
        simp [hz]
      · obtain ⟨c,hc,hbc⟩ := even_unit_two_fixed_next_phase hn4 m hn hb (hunit_at b hb) (hfixed b hb)
        have hval2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
        have hci : (cyclicOffset p c i).val=r-2 := by
          rw [cyclic_offset_reanchor p b c i,hbc,Fin.coe_sub_iff_le.mpr (show (2 : Fin n) ≤ cyclicOffset p b i by
            change (2 : Fin n).val ≤ (cyclicOffset p b i).val
            rw [hval2,hir]
            omega),hir,hval2]
        have hh' := ih (r-2) (by omega) c hc i hci
        omega
  intro b hb i
  exact main _ b hb i rfl

/-- The existence of a one-fixed-point minimal phase is geometric and
independent of any chosen LX upper-bound constant. -/
theorem even_unit_exists_one_fixed {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    ∃ b : Fin n,GlobalMinimum p b ∧ (fixedPositions (permutation p b)).card=1 := by
  classical
  by_contra hnone
  have hfixed (b : Fin n) (hb : GlobalMinimum p b) : (fixedPositions (permutation p b)).card=2 := by
    have hx := Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
    have hunitb : (inversions (displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by rwa [hx]
    have hc := (even_unit_reserve_source m hn hb hunitb).2.2.1
    rcases hc with hc | hc
    · exact False.elim (hnone ⟨b,hb,hc⟩)
    · exact hc
  let q := permutation p a
  let Q := shiftConjugate q a.val
  have hf := hfixed a ha
  have hp := even_unit_two_fixed_offsets_even hn4 m hn ha hunit hfixed a ha
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

theorem even_unit_reflection_neighbor {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    ∃ u r : Fin n,∀ i : Fin n,(p*Equiv.swap u (u+1)) i=r-i := by
  obtain ⟨b,hb,hfixed⟩ := even_unit_exists_one_fixed hn4 m hn ha hunit
  have hx := Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
  have hunitb : (inversions (displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by rwa [hx]
  exact even_unit_one_fixed_reflection_neighbor m hn hb hunitb hfixed

#print axioms even_unit_exists_one_fixed
#print axioms even_unit_reflection_neighbor
end LX.AnchoredPhases
