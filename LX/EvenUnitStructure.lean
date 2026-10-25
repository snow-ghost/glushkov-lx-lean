import LX.MinimumEnergyPhases
import LX.PairCorePorts
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every globally minimal anchor in the even unit-reserve branch has the
same height. Its own strip reserve is exactly one. -/
theorem even_unit_reserve_height {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    height p a+1=m ∧ anchorReserve p a=1 := by
  have hm := global_minimum_majorized ha
  have hh := (short_coordinates (is_lift p a).1 hm a).2
  rw [displacement_anchor] at hh
  have hdiv : n/2=m := by omega
  have hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1 := by
    rw [hdiv]
    have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
    nlinarith
  have hgap := small_dimension_reserve_height_gap p a hsmall
  have he : height p a+1=m := by omega
  refine ⟨he,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
  have he' : (height p a : ℤ)+1=m := by exact_mod_cast he
  nlinarith

/-- The unit-reserve condition constrains every actual anchor, including
anchors which are not globally minimal or majorized. -/
theorem even_unit_all_anchor_bounds {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) (b : Fin n) :
    (height p b+1=m ∨ height p b=m) ∧
      (inversions (displacement p b)=inversions (displacement p a) ∨
       inversions (displacement p b)=inversions (displacement p a)+1) ∧
      (anchorReserve p b=0 ∨ anchorReserve p b=1) := by
  have hx := (candidate_price_components p b).1
  have hlo := global_minimum_exchanges ha b
  have hlo' : (inversions (displacement p a) : ℤ) ≤ inversions (displacement p b) := by
    exact_mod_cast hlo
  have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
  have hsq : (2*(height p b : ℤ)-(2*(m : ℤ)-1))^2 ≤ 5 := by nlinarith
  have hh : height p b+1=m ∨ height p b=m := by
    by_contra hnot
    have hsep : 3 ≤ 2*(height p b : ℤ)-(2*(m : ℤ)-1) ∨
        2*(height p b : ℤ)-(2*(m : ℤ)-1) ≤ -3 := by omega
    rcases hsep with hp | hp
    · nlinarith [sq_nonneg (2*(height p b : ℤ)-(2*(m : ℤ)-1)-3)]
    · nlinarith [sq_nonneg (2*(height p b : ℤ)-(2*(m : ℤ)-1)+3)]
  have hcap : (height p b : ℤ)*((n : ℤ)-height p b-1)=(m : ℤ)*(m-1) := by
    rcases hh with hh | hh
    · have hh' : (height p b : ℤ)+1=m := by exact_mod_cast hh
      nlinarith
    · rw [hh,hn']
      ring
  rw [hcap] at hx
  refine ⟨hh,by omega,?_⟩
  unfold anchorReserve
  rw [hcap]
  omega


/-- Exact rank and fixed-point constraints, extracted from the actual input.
The two possible fixed-point counts give one or two units of cycle excess. -/
theorem even_unit_reserve_source {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    let q := permutation p a
    LRX.FiniteCuts.cycleDefect q=0 ∧
      q.support.card=q.cycleFactorsFinset.card+m ∧
      ((LRX.FiniteCuts.fixedPositions q).card=1 ∨
       (LRX.FiniteCuts.fixedPositions q).card=2) ∧
      q.support.card=2*q.cycleFactorsFinset.card+
        (LRX.FiniteCuts.fixedPositions q).card := by
  obtain ⟨hh,hr⟩ := even_unit_reserve_height m hn ha hunit
  obtain ⟨hz,hrank,_,_,_⟩ := unit_anchor_reserve_rigidity p a
    (global_minimum_majorized ha) hr
  have hf := majorized_anchor_fixed_positions p a (global_minimum_majorized ha)
  have hcard := LRX.FiniteCuts.fixed_positions_card (permutation p a)
  have hpos : 0 < (LRX.FiniteCuts.fixedPositions (permutation p a)).card := by
    apply Finset.card_pos.mpr
    exact ⟨a,(LRX.FiniteCuts.mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
  dsimp only
  exact ⟨hz,by omega,by omega,by omega⟩

/-- Number of actual disjoint cycles of a specified size. -/
def cycleSizeCount (q : State n) (k : ℕ) : ℕ :=
  (q.cycleFactorsFinset.filter (fun g => g.support.card=k)).card

/-- A small total excess bounds each cycle individually; this does not
replace the cycle factorization by an arbitrary exceptional set. -/
theorem cycle_size_le_of_excess (q : State n) (e : ℕ)
    (he : q.support.card=2*q.cycleFactorsFinset.card+e)
    (g : State n) (hg : g ∈ q.cycleFactorsFinset) : g.support.card ≤ e+2 := by
  classical
  have hsum : (∑ c ∈ q.cycleFactorsFinset,((c.support.card : ℤ)-2))=(e : ℤ) := by
    rw [Finset.sum_sub_distrib]
    have hs : (∑ c ∈ q.cycleFactorsFinset,(c.support.card : ℤ))=(q.support.card : ℤ) := by
      exact_mod_cast LRX.FiniteCuts.cycle_support_card_sum q
    rw [hs,he]
    simp
    ring
  have hle := Finset.single_le_sum (f := fun c : State n => (c.support.card : ℤ)-2)
    (fun c hc => by
      have hh := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
      omega) hg
  rw [hsum] at hle
  omega

/-- With at most two units of cycle excess, the only non-pair cycles are
triangles and quadrilaterals, with their exact weighted count. -/
theorem small_cycle_excess_profile (q : State n) (e : ℕ) (he2 : e ≤ 2)
    (he : q.support.card=2*q.cycleFactorsFinset.card+e) :
    (∀ g ∈ q.cycleFactorsFinset,g.support.card=2 ∨ g.support.card=3 ∨ g.support.card=4) ∧
      cycleSizeCount q 3+2*cycleSizeCount q 4=e := by
  classical
  have hsize (g : State n) (hg : g ∈ q.cycleFactorsFinset) :
      g.support.card=2 ∨ g.support.card=3 ∨ g.support.card=4 := by
    have hlo := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1.two_le_card_support
    have hhi := cycle_size_le_of_excess q e he g hg
    omega
  refine ⟨hsize,?_⟩
  have hterm (g : State n) (hg : g ∈ q.cycleFactorsFinset) :
      g.support.card=2+(if g.support.card=3 then 1 else 0)+
        2*(if g.support.card=4 then 1 else 0) := by
    rcases hsize g hg with h | h | h <;> simp [h]
  have hs := Finset.sum_congr rfl hterm
  rw [LRX.FiniteCuts.cycle_support_card_sum] at hs
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    smul_eq_mul,Finset.sum_boole] at hs
  change q.support.card=q.cycleFactorsFinset.card*2+cycleSizeCount q 3+
    2*cycleSizeCount q 4 at hs
  omega


#print axioms even_unit_reserve_height
#print axioms even_unit_all_anchor_bounds
#print axioms even_unit_reserve_source
end LX.AnchoredPhases
