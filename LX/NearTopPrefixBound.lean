import LX.ForwardPrefixBudget
import LX.MinimumHeightPrefix
import LX.NearTopPrefix
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.FiniteDropBudget LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem near_top_prefix_forward (p : State n) (a : Fin n) (r : ℕ)
    (hh : 2 ≤ height p a) (hhead : permutation p a 0 ≠ 0)
    (hpre : ∀ i : Fin n,i.val < r → height p a-1 ≤ backwardDepth (displacement p a) i) :
    ForwardPrefix (permutation p a) r := by
  intro i hir
  have hi := near_top_prefix_nondecreasing p a r hh hhead hpre i hir
  refine ⟨hi,?_⟩
  intro j hij hjp
  have himove : permutation p a i ≠ i := by intro he; rw [he] at hjp; omega
  have hmax : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  have hne : backwardDepth (displacement p a) i ≠ height p a := by
    intro he
    exact himove ((depth_eq_height_iff_fixed p a i).mp he)
  have harc := (near_top_open_arc_fixed p a i (by omega) (by have := hpre i hir; omega)).2
  apply harc j
  · rw [Fin.coe_sub_iff_le.mpr (show i ≤ j by exact le_of_lt hij)]
    omega
  · rw [Fin.coe_sub_iff_le.mpr (show i ≤ j by exact le_of_lt hij),
      Fin.coe_sub_iff_le.mpr (show i ≤ permutation p a i from hi)]
    omega

/-- Minimum height bounds a prefix at the top two depths by the actual
anchor reserve, with only one additional position for its moving head. -/
theorem minimum_height_near_top_prefix_bound (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hh : 2 ≤ height p a)
    (hhead : permutation p a 0 ≠ 0) (r : ℕ) (hr : r ≤ n)
    (hpre : ∀ i : Fin n,i.val < r → height p a-1 ≤ backwardDepth (displacement p a) i) :
    (r : ℤ) ≤ (n : ℤ)-2*height p a+anchorReserve p a+1 := by
  by_cases hr0 : r=0
  · subst r
    have hb := minimum_height_fixed_prefix_bound p a hmin 0 (NeZero.pos n)
      (by intro i hi; omega)
    omega
  have hf := near_top_prefix_forward p a r hh hhead hpre
  have hd := forward_prefix_drop_bound (permutation p a) r (by omega) hr hf hhead hh
  have hu := minimum_height_backward_units p a hmin
  have he := anchor_reserve_decomposition p a
  unfold cycleDefect at he
  change 3*(height p a : ℤ) ≤ _ at hd
  omega

/-- A low-depth position occurs within the reserve-controlled prefix.
This is an existence theorem for the actual anchored permutation. -/
theorem minimum_height_early_low_depth (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hh : 2 ≤ height p a)
    (hhead : permutation p a 0 ≠ 0) :
    ∃ i : Fin n,backwardDepth (displacement p a) i < height p a-1 ∧
      (i.val : ℤ) ≤ (n : ℤ)-2*height p a+anchorReserve p a+1 := by
  classical
  let S := Finset.univ.filter fun i : Fin n => backwardDepth (displacement p a) i < height p a-1
  have hS : S.Nonempty := by
    by_contra hn
    have hpre (i : Fin n) (_ : i.val < n) : height p a-1 ≤ backwardDepth (displacement p a) i := by
      by_contra hi
      exact hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩⟩
    have hmono := near_top_prefix_nondecreasing p a n hh hhead hpre
    have hd : (descendingPositions (permutation p a)).Nonempty := Finset.card_pos.mp (by
      change 0 < height p a
      omega)
    obtain ⟨i,hi⟩ := hd
    have hb := (mem_descendingPositions _ _).mp hi
    have hf := hmono i i.isLt
    omega
  let i := S.min' hS
  have hi : i ∈ S := Finset.min'_mem S hS
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  apply minimum_height_near_top_prefix_bound p a hmin hh hhead i.val (Nat.le_of_lt i.isLt)
  intro j hj
  by_contra hnot
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have hle : i ≤ j := Finset.min'_le S j hjS
  change i.val ≤ j.val at hle
  omega


#print axioms minimum_height_near_top_prefix_bound
#print axioms minimum_height_early_low_depth
end LX.AnchoredPhases
