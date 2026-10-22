import LX.SingleHeadQuadraticUpper

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Retain the actual fixed fiber instead of replacing it by a second peak. -/
theorem rank_peak_next_depth_fiber (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (b : Fin n) (hh : 0 < height p b) :
    (depthCount (displacement p b) (height p b-1) : ℤ)+height p b ≤
      (height p a : ℤ)+R+(fixedPositions (permutation p b)).card+2 := by
  classical
  let f := (fixedPositions (permutation p b)).card
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
  have hb := rank_peak_below_count p a R hR b (f+2)
  dsimp only [f] at *
  omega

/-- The separation, not only the larger gap, bounds an equal-height fiber. -/
theorem gap_separation_bounds_fixed (p : State n) (a b : Fin n)
    (hh : height p b=height p a) (hg : (b-p b).val < (a-p a).val) :
    (fixedPositions (permutation p a)).card+(b-p b).val ≤ (a-p a).val := by
  have hoff : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    rw [hoff,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hg.le)]
  have he := reanchor_height p a b
  have hcount : belowCount p a (cyclicOffset p a b).val=(cyclicOffset p a b).val := by omega
  have hf : (fixedPositions (permutation p a)).card ≤ belowCount p a (cyclicOffset p a b).val := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p a i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  omega

/-- Choose a least gap in a prescribed height class and terminal range.
The fallback is irrelevant when that class is empty. -/
theorem exists_least_gap_above (p : State n) (h J : ℕ) :
    ∃ b : Fin n,∀ c,height p c=h → J ≤ (c-p c).val →
      height p b=h ∧ J ≤ (b-p b).val ∧ (b-p b).val ≤ (c-p c).val := by
  classical
  let S := Finset.univ.filter fun c : Fin n => height p c=h ∧ J ≤ (c-p c).val
  by_cases hs : S.Nonempty
  · obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image S (fun c => (c-p c).val) hs
    have hb' := (Finset.mem_filter.mp hb).2
    exact ⟨b,fun c hc hg => ⟨hb'.1,hb'.2,hmin c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hg⟩)⟩⟩
  · exact ⟨0,fun c hc hg => False.elim (hs ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hg⟩⟩)⟩

omit [NeZero n] in
/-- Two non-head forward arrows cannot simultaneously have the two
largest possible non-head differences. -/
theorem missing_large_forward_difference (p : State n) (hn : 4 ≤ n) :
    ∃ q : ℕ,q ∈ Finset.Icc (n-4) (n-2) ∧
      ∀ i : Fin n,0 < i.val → i.val < (p i).val → (p i).val-i.val ≠ q := by
  by_cases hex : ∃ i : Fin n,0 < i.val ∧ (p i).val-i.val=n-2
  · obtain ⟨i,hi,hd⟩ := hex
    have hin := i.isLt
    have hpin := (p i).isLt
    have hiv : i.val=1 := by omega
    have hpiv : (p i).val=n-1 := by omega
    refine ⟨n-3,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    intro j hj hjp he
    have hjn := j.isLt
    have hpjn := (p j).isLt
    have hjcase : j.val=1 ∨ (p j).val=n-1 := by omega
    rcases hjcase with hjcase | hjcase
    · have hji : j=i := Fin.ext (by omega)
      subst j
      omega
    · have hji : j=i := p.injective (Fin.ext (by omega))
      subst j
      omega
  · refine ⟨n-2,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,?_⟩
    intro i hi _ he
    exact hex ⟨i,hi,he⟩

#print axioms rank_peak_next_depth_fiber
#print axioms gap_separation_bounds_fixed
#print axioms exists_least_gap_above
#print axioms missing_large_forward_difference
end LX.AnchoredPhases
