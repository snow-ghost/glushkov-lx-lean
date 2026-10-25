import LX.AllGlobalOddGeometry
import LX.EvenSecondFewFixed
import LX.NearMinimumPhases
import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The height at any threshold, including an unoccupied one, is its
shifted offset mass. -/
theorem shifted_offset_rank_mass (p : State n) (a t : Fin n) :
    (∑ i : Fin n, ((cyclicOffset p a i-t : Fin n) : ℤ))=
      (n : ℤ)*((height p a : ℤ)+rankSurplus p a t.val) := by
  have hc : (∑ i : Fin n,if (cyclicOffset p a i).val < t.val then (n : ℤ) else 0)=
      (n : ℤ)*belowCount p a t.val := by
    rw [← Finset.sum_filter]
    simp [belowCount,mul_comm]
  simp_rw [cyclic_subtraction_value]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cyclic_offset_mass,hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,rankSurplus]
  ring

/-- Reanchoring translates the full rank profile, including every gap. -/
theorem rank_profile_reanchor (p : State n) (a b t : Fin n) :
    (height p b : ℤ)+rankSurplus p b t.val=
      (height p a : ℤ)+rankSurplus p a (cyclicOffset p a b+t).val := by
  have hb := shifted_offset_rank_mass p b t
  have ha := shifted_offset_rank_mass p a (cyclicOffset p a b+t)
  have he (i : Fin n) : cyclicOffset p b i-t=
      cyclicOffset p a i-(cyclicOffset p a b+t) := by
    rw [cyclic_offset_reanchor p a b i]
    ring
  simp_rw [he] at hb
  exact mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n) (hb.symm.trans ha)

theorem rank_peak_below_count (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) (b : Fin n) (t : ℕ) :
    (belowCount p b t : ℤ)+height p b ≤ (t : ℤ)+height p a+R := by
  by_cases ht : t < n
  · have he := rank_profile_reanchor p a b ⟨t,ht⟩
    have hr := hR (cyclicOffset p a b+⟨t,ht⟩)
    have hs : (height p b : ℤ)+rankSurplus p b t ≤ (height p a : ℤ)+R :=
      he.trans_le (by omega)
    unfold rankSurplus at hs
    omega
  · have hr := hR (cyclicOffset p a b)
    have hh := reanchor_height p a b
    have hc : belowCount p b t ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    unfold rankSurplus at hr
    omega

theorem rank_peak_fixed_count (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) (b : Fin n) :
    ((fixedPositions (permutation p b)).card : ℤ)+height p b ≤ (height p a : ℤ)+R+1 := by
  have hc := rank_peak_below_count p a R hR b 1
  have he : belowCount p b 1=(fixedPositions (permutation p b)).card := by
    unfold belowCount
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_fixedPositions]
    rw [← offset_zero_iff_source_fixed,Fin.ext_iff]
    simp only [Fin.val_zero]
    omega
  rw [he] at hc
  omega

/-- The next-depth count and the height rise spend the same rank peak. -/
theorem rank_peak_next_depth (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (b : Fin n) (hh : 0 < height p b) :
    (depthCount (displacement p b) (height p b-1) : ℤ)+2*height p b ≤
      2*(height p a : ℤ)+2*R+3 := by
  classical
  let f := (fixedPositions (permutation p b)).card
  have hsub : Finset.univ.filter (fun i => height p b-1 ≤ backwardDepth (displacement p b) i) ⊆
      Finset.univ.filter (fun i => (cyclicOffset p b i).val < f+2) := by
    intro i hi
    have hdepth := (Finset.mem_filter.mp hi).2
    have hw := displacement_depth_width_bound (is_lift p b)
      (fun i j => (displacement_strict_width p b i j).le) (height p b-1) i
      (Finset.mem_filter.mp hi).2
    rw [show height p b-1+1=height p b by omega,displacement_offset,top_depth_count_eq_fixed] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [f]; omega⟩
  have hc := Finset.card_le_card hsub
  change depthCount (displacement p b) (height p b-1) ≤ belowCount p b (f+2) at hc
  have hb := rank_peak_below_count p a R hR b (f+2)
  have hf := rank_peak_fixed_count p a R hR b
  dsimp only [f] at *
  omega

theorem rank_peak_descending_count (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) :
    (descendingPositions p).card ≤ height p a+R := by
  let t : Fin n := -(p a-a)
  have hm := shifted_offset_rank_mass p a t
  have he (i : Fin n) : cyclicOffset p a i-t=p i-i := by dsimp [cyclicOffset,t]; ring
  simp_rw [he] at hm
  rw [raw_offset_mass] at hm
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr := hR t
  nlinarith

#print axioms rank_profile_reanchor
#print axioms rank_peak_next_depth
#print axioms rank_peak_descending_count
end LX.AnchoredPhases
