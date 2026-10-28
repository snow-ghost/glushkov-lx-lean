import LX.EvenConstantHeightObstruction
import LX.MaximalOffsetDrops
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_constant_unpaid_offset_backward (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12)
    (t : Fin n) (ht : t ∈ rawOffsets p) (ht0 : t ≠ 0) (hth : t ≠ p 0) :
    ∃ i : Fin n,i ∈ descendingPositions p ∧ p i-i=t := by
  obtain ⟨b,_,hbt⟩ := Finset.mem_image.mp ht
  obtain ⟨c,hraw,_,_,hlast⟩ := last_offset_source p b
  have hct : p c-c=t := hraw.trans hbt
  by_cases hback : (p c).val < c.val
  · exact ⟨c,(mem_descendingPositions _ _).mpr hback,hct⟩
  have hforward : c.val < (p c).val := by
    by_contra hnot
    have he : p c=c := Fin.ext (by omega)
    rw [he,sub_self] at hct
    exact ht0 hct.symm
  have hhead : p 0 ≠ p c-c := by
    intro he
    exact hth (hct.symm.trans he.symm)
  obtain ⟨w,hw,hprice⟩ := forward_minimum_conjecture_word p c 0 (by omega)
    (by rw [hall]; omega) (by rw [hall]; exact hh)
    (fun b => by rw [hall c,hall b]) hforward hhead hlast
  exact False.elim (hunpaid ⟨w,hw,by simpa using hprice⟩)

theorem even_constant_unpaid_raw_count_height (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (rawOffsets p).card ≤ h+2 := by
  classical
  by_cases hz : (0 : Fin n) ∈ rawOffsets p
  · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    have hpa : p a=a := sub_eq_zero.mp ha
    have he : permutation p a=p := by ext i; simp [permutation,hpa]
    have hheight := hall a
    change (descendingPositions (permutation p a)).card=h at hheight
    rw [he] at hheight
    have hc := even_constant_unpaid_raw_count p h hall hh hn hunpaid
    omega
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => (p i-i).val) ⟨0,Finset.mem_univ _⟩
  let D := descendingPositions p \ fixedPositions (permutation p a)
  let V := D.image (fun i => p i-i)
  have hsub : rawOffsets p ⊆ V ∪ {p a-a,p 0} := by
    intro t ht
    by_cases hex : t ∈ ({p a-a,p 0} : Finset (Fin n))
    · exact Finset.mem_union_right _ hex
    have ht0 : t ≠ 0 := by intro he; subst t; exact hz ht
    have hth : t ≠ p 0 := by intro he; exact hex (by simp [he])
    obtain ⟨i,hi,hraw⟩ := even_constant_unpaid_offset_backward p h hall hh hn hunpaid t ht ht0 hth
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_sdiff.mpr ⟨hi,?_⟩,hraw⟩
    intro hif
    have hf := (mem_fixedPositions _ _).mp hif
    have he : p i-i=p a-a := by
      change p i+(a-p a)=i at hf
      linear_combination hf
    have ht' : t=p a-a := hraw.symm.trans he
    exact hex (by simp [ht'])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {p a-a,p 0})
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd : D.card ≤ h := by
    have hb := drops_outside_maximal_offset p a (fun i => hmax i (Finset.mem_univ _))
    rwa [hall a] at hb
  have he : ({p a-a,p 0} : Finset (Fin n)).card ≤ 2 := by
    have hb := Finset.card_pair_eq_one_or_two (a := p a-a) (b := p 0)
    omega
  omega

/-- An actual unpaid even constant-height permutation must have maximum
fixed-fiber size exactly three. Fibers of size four are also excluded. -/
theorem even_constant_unpaid_maximum_fiber_three (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    ∃ b : Fin n,(fixedPositions (permutation p b)).card=3 ∧
      ∀ a,(fixedPositions (permutation p a)).card ≤ 3 := by
  classical
  obtain ⟨b,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun b => (fixedPositions (permutation p b)).card) ⟨0,Finset.mem_univ _⟩
  have hmax' (a : Fin n) := hmax a (Finset.mem_univ _)
  have hlo := (even_constant_unpaid_fiber_range p h hall hh hn b hmax' hunpaid).1
  have hraw := even_constant_unpaid_raw_count_height p h hall hh hn hunpaid
  have hcount := even_raw_offset_count_with_fixed p b
    (fun c => by rw [hall b,hall c]) (by rw [hall b]; exact hn)
  have hn' : (n : ℤ)=2*(h : ℤ)+2 := by exact_mod_cast hn
  have hr : ((rawOffsets p).card : ℤ) ≤ (h : ℤ)+2 := by exact_mod_cast hraw
  have he : (fixedPositions (permutation p b)).card=3 := by
    by_contra hnot
    have hbig : (4 : ℤ) ≤ (fixedPositions (permutation p b)).card := by omega
    have hpos := mul_pos (show (0 : ℤ) < (fixedPositions (permutation p b)).card by omega)
      (show (0 : ℤ) < (fixedPositions (permutation p b)).card-3 by omega)
    nlinarith only [hcount,hn',hr,hpos]
  exact ⟨b,he,fun a => by have := hmax' a; omega⟩

#print axioms even_constant_unpaid_raw_count_height
#print axioms even_constant_unpaid_maximum_fiber_three
end LX.AnchoredPhases
