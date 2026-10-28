import LX.EvenConstantThreeFiber
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A last offset representative of an unpaid input must move backward
to a positive position, except for the zero and head offsets. -/
theorem even_constant_unpaid_positive_backward (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12)
    (t : Fin n) (ht : t ∈ rawOffsets p) (ht0 : t ≠ 0) (hth : t ≠ p 0) :
    ∃ i : Fin n,i ∈ descendingPositions p ∧ p i ≠ 0 ∧ p i-i=t := by
  obtain ⟨b,_,hbt⟩ := Finset.mem_image.mp ht
  obtain ⟨c,hraw,_,_,hlast⟩ := last_offset_source p b
  have hct : p c-c=t := hraw.trans hbt
  have hhead : p 0 ≠ p c-c := by
    intro he
    exact hth (hct.symm.trans he.symm)
  have hzero : p c ≠ 0 := by
    intro hz
    obtain ⟨w,hw,hprice⟩ := zero_image_minimum_conjecture_word p c 0 (by omega)
      (by rw [hall]; omega) (by rw [hall]; exact hh)
      (fun b => by rw [hall c,hall b]) hz hhead hlast
    exact hunpaid ⟨w,hw,by simpa using hprice⟩
  by_cases hback : (p c).val < c.val
  · exact ⟨c,(mem_descendingPositions _ _).mpr hback,hzero,hct⟩
  have hforward : c.val < (p c).val := by
    by_contra hnot
    have he : p c=c := Fin.ext (by omega)
    rw [he,sub_self] at hct
    exact ht0 hct.symm
  obtain ⟨w,hw,hprice⟩ := forward_minimum_conjecture_word p c 0 (by omega)
    (by rw [hall]; omega) (by rw [hall]; exact hh)
    (fun b => by rw [hall c,hall b]) hforward hhead hlast
  exact False.elim (hunpaid ⟨w,hw,by simpa using hprice⟩)

/-- Retaining the head and the zero-image token improves the unpaid
offset count by one, which excludes the remaining triple fiber. -/
theorem even_constant_unpaid_raw_count_pred (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (rawOffsets p).card ≤ h+1 := by
  classical
  by_cases hz : (0 : Fin n) ∈ rawOffsets p
  · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    have hpa : p a=a := sub_eq_zero.mp ha
    have he : permutation p a=p := by ext i; simp [permutation,hpa]
    have hheight := hall a
    change (descendingPositions (permutation p a)).card=h at hheight
    rw [he] at hheight
    let D := (descendingPositions p).erase (p.symm 0)
    let V := D.image (fun i => p i-i)
    have hsub : rawOffsets p ⊆ V ∪ {0,p 0} := by
      intro t ht
      by_cases hex : t ∈ ({0,p 0} : Finset (Fin n))
      · exact Finset.mem_union_right _ hex
      have ht0 : t ≠ 0 := by intro he; exact hex (by simp [he])
      have hth : t ≠ p 0 := by intro he; exact hex (by simp [he])
      obtain ⟨i,hi,hpi,hraw⟩ := even_constant_unpaid_positive_backward p h hall hh hn hunpaid t ht ht0 hth
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr
        ⟨(fun he => hpi (by rw [he,Equiv.apply_symm_apply])),hi⟩,hraw⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {0,p 0})
    have hv : V.card ≤ D.card := Finset.card_image_le
    by_cases hp0 : p 0=0
    · simp only [hp0,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton] at hc
      have hd : D.card ≤ h := (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq hheight
      omega
    · have hpre : p.symm 0 ≠ 0 := by
        intro he
        have he' := congrArg p he
        simp only [Equiv.apply_symm_apply] at he'
        exact hp0 he'.symm
      have hmem : p.symm 0 ∈ descendingPositions p := by
        rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
        exact Fin.pos_iff_ne_zero.mpr hpre
      have hd : D.card=h-1 := by dsimp only [D]; rw [Finset.card_erase_of_mem hmem,hheight]
      have hp := Finset.card_pair_eq_one_or_two (a := (0 : Fin n)) (b := p 0)
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
  have hd := drops_outside_maximal_offset_head p a (fun i => hmax i (Finset.mem_univ _))
  rw [hall a] at hd
  change D.card+(if p 0=p a-a then 0 else 1) ≤ h at hd
  by_cases hp0 : p 0=p a-a
  · simp only [hp0,ite_true,add_zero] at hd
    rw [← hp0] at hc
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton] at hc
    omega
  · rw [ite_eq_right hp0] at hd
    have hp := Finset.card_pair_eq_one_or_two (a := p a-a) (b := p 0)
    omega

/-- The full critical constant-height even family is paid at constant 3. -/
theorem even_critical_constant_conjecture_word (p : State n) (h : ℕ)
    (hall : ∀ a,height p a=h) (hh : 2 ≤ h) (hn : n=2*h+2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_contra hunpaid
  have hc := even_constant_unpaid_raw_count_pred p h hall hh hn hunpaid
  obtain ⟨b,hb,_⟩ := even_constant_unpaid_maximum_fiber_three p h hall hh hn hunpaid
  have hlow := even_raw_offset_count_with_fixed p b
    (fun c => by rw [hall b,hall c]) (by rw [hall b]; exact hn)
  rw [hb] at hlow
  norm_num at hlow
  omega


#print axioms even_critical_constant_conjecture_word
end LX.AnchoredPhases
