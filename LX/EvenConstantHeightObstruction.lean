import LX.ConstantHeightEvenGeometry
import LX.CriticalPhaseWord
import LX.ForwardMinimumConjecture
import LX.MinimumHeightMultiplicity
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_constant_two_fibers_conjecture_word (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 0 < h) (hn : n=2*h+2)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ 2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  let r : Fin n := -1
  obtain ⟨c,hc⟩ := constant_height_predecessor p h 2 hall hF hh r
  have h1val : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have he : c-p c=(1 : Fin n)+(r-(p c-c)) := by dsimp only [r]; ring
  have hgap : (c-p c).val=1+(r-(p c-c)).val := by
    rw [he,Fin.val_add,h1val,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p c
    (by rw [hall]; exact hn) (by rw [hall]; exact hh) (by have := hF c; omega)
  have hr := anchor_reserve_nonneg p c
  exact ⟨w,hw,by omega⟩

/-- With the new forward-prefix bound, only the zero offset and the head
offset can avoid a backward representative in an unpaid constant-height
input. The former exclusion of a whole terminal interval is unnecessary. -/
theorem even_constant_unpaid_raw_count (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (rawOffsets p).card ≤ (descendingPositions p).card+2 := by
  classical
  let V := (descendingPositions p).image (fun i => p i-i)
  have hsub : rawOffsets p ⊆ V ∪ {0,p 0} := by
    intro t ht
    by_cases hex : t ∈ ({0,p 0} : Finset (Fin n))
    · exact Finset.mem_union_right _ hex
    obtain ⟨b,_,hbt⟩ := Finset.mem_image.mp ht
    obtain ⟨c,hraw,_,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    by_cases hback : (p c).val < c.val
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨c,(mem_descendingPositions _ _).mpr hback,hct⟩)
    have hforward : c.val < (p c).val := by
      by_contra hnot
      have he : p c=c := Fin.ext (by omega)
      have ht0 : t=0 := by rw [he,sub_self] at hct; exact hct.symm
      exact hex (by simp [ht0])
    have hhead : p 0 ≠ p c-c := by
      intro he
      have ht0 : t=p 0 := hct.symm.trans he.symm
      exact hex (by simp [ht0])
    obtain ⟨w,hw,hprice⟩ := forward_minimum_conjecture_word p c 0 (by omega)
      (by rw [hall]; omega) (by rw [hall]; exact hh)
      (fun b => by rw [hall c,hall b]) hforward hhead hlast
    exact False.elim (hunpaid ⟨w,hw,by simpa using hprice⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {0,p 0})
  have hv : V.card ≤ (descendingPositions p).card := Finset.card_image_le
  have he : ({0,p 0} : Finset (Fin n)).card ≤ 2 := by
    have hh := Finset.card_pair_eq_one_or_two (a := (0 : Fin n)) (b := p 0)
    omega
  omega

/-- The remaining even constant-height case has maximum fiber size only
three or four; both bounds follow for actual unpaid permutations. -/
theorem even_constant_unpaid_fiber_range (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (b : Fin n) (hmax : ∀ a,(fixedPositions (permutation p a)).card ≤
      (fixedPositions (permutation p b)).card)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    3 ≤ (fixedPositions (permutation p b)).card ∧
      (fixedPositions (permutation p b)).card ≤ 4 := by
  let F := (fixedPositions (permutation p b)).card
  have hlow : 3 ≤ F := by
    by_contra hnot
    exact hunpaid (even_constant_two_fibers_conjecture_word p h hall (by omega) hn
      (fun a => (hmax a).trans (by omega)))
  have hlo := even_raw_offset_count_with_fixed p b
    (fun c => by rw [hall b,hall c]) (by rw [hall b]; exact hn)
  have hhi := even_constant_unpaid_raw_count p h hall hh hn hunpaid
  have hdesc := constant_height_descending_bound p h F hall hmax hn
  change (n : ℤ)+((F : ℤ)-1)*(F-2) ≤ 2*((rawOffsets p).card : ℤ) at hlo
  have hn' : (n : ℤ)=2*(h : ℤ)+2 := by exact_mod_cast hn
  have hc : ((rawOffsets p).card : ℤ) ≤ (h : ℤ)+F+1 := by omega
  refine ⟨hlow,?_⟩
  change F ≤ 4
  by_contra hnot
  have hp := mul_nonneg (show 0 ≤ (F : ℤ)-5 by omega) (show 0 ≤ (F : ℤ) by positivity)
  nlinarith only [hlo,hn',hc,hp]

#print axioms even_constant_two_fibers_conjecture_word
#print axioms even_constant_unpaid_raw_count
#print axioms even_constant_unpaid_fiber_range
end LX.AnchoredPhases
