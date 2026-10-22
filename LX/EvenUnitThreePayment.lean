import LX.SingleThreeReflection

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The one-fixed-position even unit-reserve input is a circular reflection
with one neighboring-position swap. All shape hypotheses come from the source. -/
theorem even_unit_one_fixed_reflection_neighbor {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hfixed : (fixedPositions (permutation p a)).card=1) :
    ∃ u r : Fin n,∀ i : Fin n,(p*Equiv.swap u (u+1)) i=r-i := by
  let q := permutation p a
  let Q := shiftConjugate q a.val
  obtain ⟨hz,_,_,he⟩ := even_unit_reserve_source m hn ha hunit
  rw [hfixed] at he
  have hh := (even_unit_reserve_height m hn ha hunit).1
  have hqback := even_source_no_backward_unit p a (global_minimum_majorized ha)
    (by omega : n=2*height p a+2)
  have hqfixed (i : Fin n) (hi : q i=i) : i=a :=
    Finset.card_le_one.mp hfixed.le i ((mem_fixedPositions _ _).mpr hi) a
      ((mem_fixedPositions _ _).mpr (permutation_anchor p a))
  have hQzero : cycleDefect Q=0 := by
    dsimp only [Q]
    rw [LX.CycleGeometry.shift_cycle_defect]
    exact hz
  obtain ⟨hs,hc⟩ := LX.CycleGeometry.shift_support_and_cycle_count q a.val
  have hQexcess : Q.support.card=2*Q.cycleFactorsFinset.card+1 := by
    dsimp only [Q]
    rw [hs,hc]
    exact he
  have hQ0 : Q 0=0 := by
    simp only [Q,q,shift_conjugate_apply,zero_add,permutation_anchor,sub_self]
  have hQfixed (i : Fin n) (hi : Q i=i) : i=0 := by
    have hh := congrArg (fun j : Fin n => j+a) hi
    simp only [Q,shift_conjugate_apply,sub_add_cancel] at hh
    have he' := hqfixed (i+a) hh
    exact add_right_cancel (show i+a=0+a by simpa using he')
  have hQback (i j : Fin n) (hij : i.val+1=j.val) : Q j ≠ i := by
    intro hi
    have hj : i+1=j := LX.MatchingGeometry.eq_add_of_value_add i j 1 hij
    rw [← hj] at hi
    have hh := congrArg (fun j : Fin n => j+a) hi
    simp only [Q,shift_conjugate_apply,sub_add_cancel] at hh
    have harg : i+1+a=(i+a)+1 := by ring
    rw [harg] at hh
    exact hqback (i+a) hh
  obtain ⟨u,v,huv,href⟩ := LX.CycleGeometry.single_three_neighbor_reflection_at_zero
    Q hQzero hQexcess hQ0 hQfixed hQback
  have hv : v=u+1 := (LX.MatchingGeometry.eq_add_of_value_add u v 1 huv).symm
  have hva : v+a=(u+a)+1 := by rw [hv]; ring
  refine ⟨u+a,a+p a,?_⟩
  intro i
  have hswap : Equiv.swap (u+a) ((u+a)+1) i=Equiv.swap u v (i-a)+a := by
    have hs := Function.Injective.map_swap (f := fun j : Fin n => j+a)
      (add_left_injective a) u v (i-a)
    simpa only [sub_add_cancel,hva] using hs.symm
  have hh := href (i-a)
  change shiftConjugate q a.val (Equiv.swap u v (i-a))= -(i-a) at hh
  rw [shift_conjugate_apply,← hswap] at hh
  change p (Equiv.swap (u+a) ((u+a)+1) i)+(a-p a)-a= -(i-a) at hh
  change p (Equiv.swap (u+a) ((u+a)+1) i)=a+p a-i
  linear_combination hh

/-- Full LX payment of the even unit-reserve subcase having a globally
minimal source with exactly one fixed position. -/
theorem even_unit_one_fixed_upper_word {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hfixed : (fixedPositions (permutation p a)).card=1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨u,r,hr⟩ := even_unit_one_fixed_reflection_neighbor m hn ha hunit hfixed
  obtain ⟨w,hw,hprice⟩ := reflection_neighbor_upper_word hn4 (p*Equiv.swap u (u+1)) r hr u
  have he : (p*Equiv.swap u (u+1))*Equiv.swap u (u+1)=p := by simp [mul_assoc]
  rw [he] at hw
  exact ⟨w,hw,hprice⟩

/-- Any remaining even unit-reserve input has two fixed positions in every
globally minimal phase. A single exceptional phase would already pay it. -/
theorem even_unit_unpaid_all_minima_two_fixed {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∀ b : Fin n,GlobalMinimum p b → (fixedPositions (permutation p b)).card=2 := by
  intro b hb
  have hx : inversions (displacement p b)=inversions (displacement p a) :=
    Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
  have hbunit : (inversions (displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by rwa [hx]
  have hcases := (even_unit_reserve_source m hn hb hbunit).2.2.1
  rcases hcases with h | h
  · exact False.elim (hunpaid (even_unit_one_fixed_upper_word hn4 m hn hb hbunit h))
  · exact h

#print axioms even_unit_one_fixed_reflection_neighbor
#print axioms even_unit_one_fixed_upper_word
#print axioms even_unit_unpaid_all_minima_two_fixed
end LX.AnchoredPhases
