import LX.CriticalPhaseWord
import LX.ForwardMinimumConjecture
import LX.LowOffsetDropBudget
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

def minimumRawOffsets (p : State n) (h : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun b : Fin n => height p b=h).image (fun b => p b-b)

theorem mem_minimum_raw_offsets (p : State n) (h : ℕ) (t : Fin n) :
    t ∈ minimumRawOffsets p h ↔ ∃ b : Fin n,height p b=h ∧ p b-b=t := by
  simp only [minimumRawOffsets,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The minimum-phase backward representative uses no constant-height
hypothesis; all other phases may have arbitrary larger height. -/
theorem minimum_unpaid_positive_backward (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c) (hb : height p b=height p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e)
    (ht0 : p b-b ≠ 0) (hth : p b-b ≠ p 0) :
    ∃ i : Fin n,i ∈ descendingPositions p ∧ p i ≠ 0 ∧ p i-i=p b-b := by
  obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
  have hc : height p c=height p a := hch.trans hb
  have hhead : p 0 ≠ p c-c := by intro he; exact hth (hraw.symm.trans he.symm)
  have hminc : ∀ b,height p c ≤ height p b := by intro b; rw [hc]; exact hmin b
  have hzero : p c ≠ 0 := by
    intro hz
    exact hunpaid (zero_image_minimum_conjecture_word p c e he (by omega) (by omega)
      hminc hz hhead hlast)
  by_cases hback : (p c).val < c.val
  · exact ⟨c,(mem_descendingPositions _ _).mpr hback,hzero,hraw⟩
  have hforward : c.val < (p c).val := by
    by_contra hnot
    have he : p c=c := Fin.ext (by omega)
    rw [he,sub_self] at hraw
    exact ht0 hraw.symm
  exact False.elim (hunpaid (forward_minimum_conjecture_word p c e he (by omega) (by omega)
    hminc hforward hhead hlast))

/-- In either parity, an unpaid input has at most `h+1` distinct offsets
at the minimum height. The count includes the head and zero-image cases. -/
theorem unpaid_minimum_offset_count (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e) :
    (minimumRawOffsets p (height p a)).card ≤ height p a+1 := by
  classical
  let M := minimumRawOffsets p (height p a)
  change M.card ≤ height p a+1
  by_cases hz : (0 : Fin n) ∈ M
  · obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets p (height p a) 0).mp hz
    have hpb : p b=b := sub_eq_zero.mp hraw
    have heq : permutation p b=p := by ext i; simp [permutation,hpb]
    change (descendingPositions (permutation p b)).card=height p a at hb
    rw [heq] at hb
    let D := (descendingPositions p).erase (p.symm 0)
    let V := D.image (fun i => p i-i)
    have hsub : M ⊆ V ∪ {0,p 0} := by
      intro t ht
      by_cases hex : t ∈ ({0,p 0} : Finset (Fin n))
      · exact Finset.mem_union_right _ hex
      obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
      have ht0 : p c-c ≠ 0 := by rw [hct]; intro he; exact hex (by simp [he])
      have hth : p c-c ≠ p 0 := by rw [hct]; intro he; exact hex (by simp [he])
      obtain ⟨i,hi,hpi,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid ht0 hth
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr
        ⟨(fun hi0 => hpi (by rw [hi0,Equiv.apply_symm_apply])),hi⟩,hrawi.trans hct⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {0,p 0})
    have hv : V.card ≤ D.card := Finset.card_image_le
    by_cases hp0 : p 0=0
    · simp only [hp0,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton] at hc
      have hd : D.card ≤ height p a := (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq hb
      omega
    · have hpre : p.symm 0 ≠ 0 := by
        intro heq
        have he' := congrArg p heq
        simp only [Equiv.apply_symm_apply] at he'
        exact hp0 he'.symm
      have hmem : p.symm 0 ∈ descendingPositions p := by
        rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
        exact Fin.pos_iff_ne_zero.mpr hpre
      have hd : D.card=height p a-1 := by dsimp only [D]; rw [Finset.card_erase_of_mem hmem,hb]
      have hp := Finset.card_pair_eq_one_or_two (a := (0 : Fin n)) (b := p 0)
      omega
  let S := Finset.univ.filter fun b : Fin n => height p b=height p a
  have hS : S.Nonempty := ⟨a,by simp [S]⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S (fun b => (p b-b).val) hS
  have hbh : height p b=height p a := (Finset.mem_filter.mp hb).2
  let D := lowerOffsetDrops p (p b-b)
  let V := D.image (fun i => p i-i)
  have hsub : M ⊆ V ∪ {p b-b,p 0} := by
    intro t ht
    by_cases hex : t ∈ ({p b-b,p 0} : Finset (Fin n))
    · exact Finset.mem_union_right _ hex
    obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
    have ht0 : p c-c ≠ 0 := by
      intro heq
      have htzero : t=0 := hct.symm.trans heq
      exact hz (htzero ▸ ht)
    have hth : p c-c ≠ p 0 := by rw [hct]; intro heq; exact hex (by simp [heq])
    obtain ⟨i,hi,_,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid ht0 hth
    have hcle := hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
    have hne : (p c-c).val ≠ (p b-b).val := by
      intro heq
      have ht' : t=p b-b := hct.symm.trans (Fin.ext heq)
      exact hex (by simp [ht'])
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,by rw [hrawi]; omega⟩,hrawi.trans hct⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V {p b-b,p 0})
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd := lower_offset_drop_bound p b
  rw [hbh] at hd
  change D.card+(if p 0=p b-b then 0 else 1) ≤ height p a at hd
  by_cases hp0 : p 0=p b-b
  · simp only [hp0,ite_true,add_zero] at hd
    rw [← hp0] at hc
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton] at hc
    omega
  · rw [ite_eq_right hp0] at hd
    have hp := Finset.card_pair_eq_one_or_two (a := p b-b) (b := p 0)
    omega

#print axioms unpaid_minimum_offset_count
end LX.AnchoredPhases
