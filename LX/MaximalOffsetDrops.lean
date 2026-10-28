import LX.AllGlobalOddGeometry
import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Exact ordinary drop count at a largest occupied raw offset. -/
theorem maximal_raw_offset_drop_count (p : State n) (a : Fin n)
    (hmax : ∀ i,(p i-i).val ≤ (p a-a).val) :
    ((descendingPositions p).card : ℤ)=(height p a : ℤ)+
      ((p a-a).val : ℤ)-n+(fixedPositions (permutation p a)).card := by
  classical
  let A := fixedPositions (permutation p a)
  have hAl : A.card ≤ n := (Finset.card_le_univ A).trans_eq (Fintype.card_fin n)
  have hfilter : Finset.univ.filter (fun i : Fin n => (p i-i).val < (p a-a).val)=Aᶜ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    have hm := hmax i
    have he : i ∈ A ↔ p i-i=p a-a := by
      rw [mem_fixedPositions,← offset_zero_iff_source_fixed]
      exact sub_eq_zero
    rw [he,Fin.ext_iff]
    omega
  have hsum := cyclic_offset_mass p a
  have heq (i : Fin n) : (cyclicOffset p a i : ℤ)=
      ((p i-i : Fin n) : ℤ)-((p a-a : Fin n) : ℤ)+
        if (p i-i).val < (p a-a).val then (n : ℤ) else 0 :=
    cyclic_subtraction_value (p i-i) (p a-a)
  simp_rw [heq] at hsum
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,raw_offset_mass] at hsum
  have hif : (∑ i : Fin n,if (p i-i).val < (p a-a).val then (n : ℤ) else 0)=
      (n : ℤ)*((n : ℤ)-A.card) := by
    rw [← Finset.sum_filter,hfilter]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_compl,Fintype.card_fin,
      Nat.cast_sub hAl]
    ring
  rw [hif] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hnpos : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  change ((descendingPositions p).card : ℤ)=(height p a : ℤ)+(p a-a).val-n+A.card
  nlinarith

/-- Removing the largest offset fiber leaves at most `height` ordinary
backward arrows. This retains the multiplicity discarded by raw counts. -/
theorem drops_outside_maximal_offset_head (p : State n) (a : Fin n)
    (hmax : ∀ i,(p i-i).val ≤ (p a-a).val) :
    (descendingPositions p \ fixedPositions (permutation p a)).card+
      (if p 0=p a-a then 0 else 1) ≤ height p a := by
  classical
  let A := fixedPositions (permutation p a)
  let D := descendingPositions p
  have hs : A \ D ⊆ Finset.univ.filter (fun i : Fin n => i.val < n-(p a-a).val) := by
    intro i hi
    obtain ⟨hiA,hiD⟩ := Finset.mem_sdiff.mp hi
    have hraw : p i-i=p a-a := by
      have hh := (mem_fixedPositions _ _).mp hiA
      change p i+(a-p a)=i at hh
      linear_combination hh
    have hforward : i ≤ p i := by
      have hh : ¬(p i).val < i.val := fun hh => hiD ((mem_descendingPositions _ _).mpr hh)
      change i.val ≤ (p i).val
      omega
    have hv := Fin.coe_sub_iff_le.mpr hforward
    rw [hraw] at hv
    have := (p i).isLt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have hc := Finset.card_le_card hs
  rw [Fin.card_filter_val_lt] at hc
  have hcap : (A \ D).card ≤ n-(p a-a).val := hc.trans (Nat.min_le_right _ _)
  have hA := Finset.card_sdiff_add_card_inter A D
  have hD := Finset.card_sdiff_add_card_inter D A
  rw [Finset.inter_comm D A] at hD
  have he := maximal_raw_offset_drop_count p a hmax
  change (D.card : ℤ)=(height p a : ℤ)+(p a-a).val-n+A.card at he
  have ht := (p a-a).isLt
  change (D \ A).card+(if p 0=p a-a then 0 else 1) ≤ height p a
  by_cases hhead : p 0=p a-a
  · rw [ite_eq_left hhead]
    omega
  rw [ite_eq_right hhead]
  have hz : (0 : Fin n) ∉ A := by
    intro h0
    have hf := (mem_fixedPositions _ _).mp h0
    change p 0+(a-p a)=0 at hf
    apply hhead
    linear_combination hf
  have hs' : A \ D ⊆ (Finset.univ.filter (fun i : Fin n => i.val < n-(p a-a).val)).erase 0 := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(fun he => hz (he ▸ (Finset.mem_sdiff.mp hi).1)),hs hi⟩
  have hc' := Finset.card_le_card hs'
  rw [Finset.card_erase_of_mem (by simp only [Finset.mem_filter,Finset.mem_univ,Fin.val_zero,true_and]; omega),
    Fin.card_filter_val_lt] at hc'
  omega

theorem drops_outside_maximal_offset (p : State n) (a : Fin n)
    (hmax : ∀ i,(p i-i).val ≤ (p a-a).val) :
    (descendingPositions p \ fixedPositions (permutation p a)).card ≤ height p a := by
  have hh := drops_outside_maximal_offset_head p a hmax
  omega

#print axioms maximal_raw_offset_drop_count
#print axioms drops_outside_maximal_offset
#print axioms drops_outside_maximal_offset_head
end LX.AnchoredPhases
