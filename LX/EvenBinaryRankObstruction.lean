import LX.EvenConstantHeightConjecture
import LX.MinimumOffsetCount
import LX.RankPeakCount
import LX.RankProfileGeometry
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem zero_surplus_count_le_minimum_offsets (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card ≤
      (minimumRawOffsets p (height p a)).card := by
  classical
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  have hs : Z.image (fun t => p a-a+t) ⊆ minimumRawOffsets p (height p a) := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,hh⟩ := zero_surplus_anchor p a hmin t (Finset.mem_filter.mp ht).2
    apply (mem_minimum_raw_offsets _ _ _).mpr
    refine ⟨b,hh,?_⟩
    unfold cyclicOffset at hb
    linear_combination hb
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (add_right_injective (p a-a))] at hc
  exact hc

/-- Every unpaid critical even input has a binary rank-surplus profile.
The conclusion applies also when its anchor heights vary. -/
theorem even_unpaid_rank_at_most_one (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    ∀ t : Fin n,rankSurplus p a t.val ≤ 1 := by
  classical
  have hc := unpaid_minimum_offset_count p a 0 (by omega) (by omega) hh hmin
    (by simpa using hunpaid)
  have hz := zero_surplus_count_le_minimum_offsets p a hmin
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  have hZ : Z.card ≤ height p a+1 := hz.trans hc
  let B := fun t : Fin n => if rankSurplus p a t.val=0 then (0 : ℤ) else 1
  have hB : (∑ t : Fin n,B t)=(n : ℤ)-Z.card := by
    have he (t : Fin n) : B t=1-(if rankSurplus p a t.val=0 then (1 : ℤ) else 0) := by
      dsimp only [B]
      split_ifs <;> norm_num
    simp only [he,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one,Finset.sum_boole,Z]
  have hs := rank_surplus_sum p a
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have hsum : (∑ t : Fin n,rankSurplus p a t.val)=(height p a : ℤ)+1 := by
    rw [hn'] at hs
    nlinarith only [hs]
  intro t
  by_contra hnot
  have hpoint (u : Fin n) : B u+(if u=t then (1 : ℤ) else 0) ≤ rankSurplus p a u.val := by
    have hu := rank_surplus_nonnegative p a hmin u.val (Nat.le_of_lt u.isLt)
    by_cases hut : u=t
    · subst u
      dsimp only [B]
      split_ifs <;> omega
    · dsimp only [B]
      rw [ite_eq_right hut,add_zero]
      split_ifs <;> omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint u)
  rw [Finset.sum_add_distrib,hB,hsum] at h
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  omega

/-- Only the two adjacent heights remain; higher phases have exactly one
fixed position, and some higher phase must occur. -/
theorem even_unpaid_binary_height_profile (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (∀ b,height p b=height p a ∨ height p b=height p a+1) ∧
      (∀ b,height p b=height p a+1 → (fixedPositions (permutation p b)).card=1) ∧
      ∃ b,height p b=height p a+1 := by
  have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
  have hb := (rank_peak_anchor_bounds p a 1 hmin hR).1
  refine ⟨?_,?_,?_⟩
  · intro b
    have := hb b
    omega
  · intro b hheight
    have hf := rank_peak_fixed_count p a 1 hR b
    have hpos : 0 < (fixedPositions (permutation p b)).card := Finset.card_pos.mpr
      ⟨b,(mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
    omega
  · by_contra hnot
    have hall (b : Fin n) : height p b=height p a := by
      have := hb b
      have hne : height p b ≠ height p a+1 := fun he => hnot ⟨b,he⟩
      omega
    exact hunpaid (even_critical_constant_conjecture_word p (height p a) hall hh hn)

#print axioms even_unpaid_rank_at_most_one
#print axioms even_unpaid_binary_height_profile
end LX.AnchoredPhases
