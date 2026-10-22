import LX.UniqueFixedCursor

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Maximum-depth tokens are exactly the fixed positions of the anchored
source. This identity does not require majorization. -/
theorem depth_eq_height_iff_fixed (p : State n) (a i : Fin n) :
    backwardDepth (displacement p a) i=height p a ↔ permutation p a i=i := by
  have hmax (j : Fin n) : backwardDepth (displacement p a) j ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 j
  constructor
  · intro hi
    have hh := maximum_depth_displacement (is_lift p a) i (by intro j; rw [hi]; exact hmax j)
    rw [hi,displacement_offset] at hh
    have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [cyclic_offset_normalized] at hz
    exact sub_eq_zero.mp hz
  · intro hi
    have hd := fixed_source_displacement p a i ((mem_fixedPositions _ _).mpr hi)
    have hr := displacement_add_depth (is_lift p a) i
    have hnonneg : 0 ≤ ∑ j,((LRX.AffineLift.crossing (displacement p a) i j).toNat : ℤ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    rw [hd] at hr
    have hh := hmax i
    omega

theorem top_depth_count_eq_fixed (p : State n) (a : Fin n) :
    depthCount (displacement p a) (height p a)=(fixedPositions (permutation p a)).card := by
  unfold depthCount fixedPositions
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  rw [← depth_eq_height_iff_fixed]
  omega

/-- Any nonmaximal head among the first 34 positions pays the second
even height, irrespective of global reserve or majorization. -/
theorem even_second_early_head_word (p : State n) (a r : Fin n)
    (hn : n=2*height p a+4) (hr : r.val ≤ 33)
    (hhead : backwardDepth (displacement p a) r < height p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨w,hw,hprice⟩ := word_with_nonmaximal_head (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
  have hr' : (r.val : ℤ) ≤ 33 := by omega
  exact ⟨w,hw,by nlinarith⟩

/-- A second-height phase with at most 33 fixed positions is fully paid
for every reserve size. The first suitable head is selected from the input. -/
theorem even_second_few_fixed_upper_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+4) (hf : (fixedPositions (permutation p a)).card ≤ 33) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases hz : height p a=0
  · obtain ⟨w,hw,hprice⟩ := candidate_word_bound (by omega : 2 ≤ n) p a
    rw [hz] at hprice
    norm_num at hprice
    have hn' : n=4 := by omega
    refine ⟨w,hw,?_⟩
    rw [hn'] at *
    norm_num at *
    omega
  · obtain ⟨r,hr,hhead⟩ := exists_head_with_count (displacement p a) (height p a) (by omega)
    rw [top_depth_count_eq_fixed] at hr
    exact even_second_early_head_word p a r hn (hr.trans hf) hhead

/-- In the unpaid second-height branch, the first 34 physical positions
must all be fixed. A bound on total fixed-point count alone is weaker. -/
theorem even_second_unpaid_fixed_prefix (p : State n) (a : Fin n)
    (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∀ i : Fin n,i.val ≤ 33 → permutation p a i=i := by
  intro i hi
  by_contra hnot
  have hne : backwardDepth (displacement p a) i ≠ height p a :=
    fun he => hnot ((depth_eq_height_iff_fixed p a i).mp he)
  have hh := (candidate_price_components p a).2 i
  exact hunpaid (even_second_early_head_word p a i hn hi (by omega))

#print axioms top_depth_count_eq_fixed
#print axioms even_second_few_fixed_upper_word
#print axioms even_second_unpaid_fixed_prefix
end LX.AnchoredPhases
