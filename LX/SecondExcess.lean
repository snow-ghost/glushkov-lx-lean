import LX.FiberDepthGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

def secondExcess (p : State n) (a : Fin n) : ℤ :=
  ∑ t : Fin n, max (rankSurplus p a t.val-2) 0

theorem second_excess_count (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    2*secondExcess p a =
      2*((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ)-
      2*((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ)+
      (n : ℤ)*((n : ℤ)-3-2*height p a) := by
  classical
  have he (t : Fin n) : max (rankSurplus p a t.val-2) 0 =
      rankSurplus p a t.val-1+(if rankSurplus p a t.val=0 then 1 else 0)-
        (if 2 ≤ rankSurplus p a t.val then 1 else 0) := by
    have := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
    split_ifs <;> omega
  unfold secondExcess
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hs := rank_surplus_sum p a
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hz : (∑ t : Fin n,if rankSurplus p a t.val=0 then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ) := by simp
  have hp : (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ) := by simp
  rw [hz,hp]
  nlinarith

theorem second_excess_reanchor (p : State n) (a b : Fin n)
    (hh : height p b=height p a) : secondExcess p b=secondExcess p a := by
  have he (t : Fin n) : rankSurplus p b t.val=
      rankSurplus p a (cyclicOffset p a b+t).val := by
    have := rank_profile_reanchor p a b t
    omega
  unfold secondExcess
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.addLeft (cyclicOffset p a b))
    (fun t : Fin n => max (rankSurplus p a t.val-2) 0)

/-- A height-minimum profile with peak at most four and second excess
at most three has at most nine operations at the next-to-last depth. -/
theorem small_second_excess_next_depth (p : State n) (a b : Fin n)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 4)
    (hmin : ∀ c,height p a ≤ height p c)
    (hh : height p b=height p a) (hhpos : 0 < height p b)
    (hQ : secondExcess p a ≤ 3) :
    depthCount (displacement p b) (height p b-1) ≤ 9 := by
  classical
  let f := (fixedPositions (permutation p b)).card
  have hf : f ≤ 5 := (rank_peak_anchor_bounds p a 4 hmin hR).2 b
  have hd := rank_peak_next_depth_fiber p a 4 hR b hhpos
  change (depthCount (displacement p b) (height p b-1) : ℤ)+height p b ≤
    (height p a : ℤ)+4+f+2 at hd
  by_contra hnot
  have hflo : 4 ≤ f := by omega
  have hsub : Finset.univ.filter (fun i => height p b-1 ≤ backwardDepth (displacement p b) i) ⊆
      Finset.univ.filter (fun i => (cyclicOffset p b i).val < f+2) := by
    intro i hi
    have hdepth := (Finset.mem_filter.mp hi).2
    have hw := displacement_depth_width_bound (is_lift p b)
      (fun i j => (displacement_strict_width p b i j).le) (height p b-1) i hdepth
    rw [show height p b-1+1=height p b by omega,displacement_offset,top_depth_count_eq_fixed] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [f]; omega⟩
  have hc := Finset.card_le_card hsub
  change depthCount (displacement p b) (height p b-1) ≤ belowCount p b (f+2) at hc
  have hcn : belowCount p b (f+2) ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hn : 9 < n := by omega
  have hfixed (t : ℕ) (ht : 0 < t) : f ≤ belowCount p b t := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  let S : Finset (Fin n) := {⟨1,by omega⟩,⟨2,by omega⟩,⟨6,by omega⟩,⟨7,by omega⟩}
  have hsum : (∑ t ∈ S,max (rankSurplus p b t.val-2) 0) ≤ secondExcess p b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact le_max_right _ _
  have hs : (∑ t ∈ S,max (rankSurplus p b t.val-2) 0)=
      max (rankSurplus p b 1-2) 0+max (rankSurplus p b 2-2) 0+
      max (rankSurplus p b 6-2) 0+max (rankSurplus p b 7-2) 0 := by
    simp [S,Fin.ext_iff]
    ring
  rw [hs,second_excess_reanchor p a b hh] at hsum
  have h1 := hfixed 1 (by omega)
  have h2 := hfixed 2 (by omega)
  have h67 := below_count_mono p b (show 6 ≤ 7 by omega)
  have hfcase : f=4 ∨ f=5 := by omega
  rcases hfcase with hfcase | hfcase
  all_goals rw [hfcase] at hc
  all_goals norm_num at hc
  all_goals unfold rankSurplus at hsum
  all_goals omega

#print axioms second_excess_count
#print axioms second_excess_reanchor
#print axioms small_second_excess_next_depth
end LX.AnchoredPhases
