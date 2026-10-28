import LX.EvenUnitPhaseParity
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem offset_zero_iff_source_fixed (p : State n) (a i : Fin n) :
    cyclicOffset p a i=0 ↔ permutation p a i=i := by
  rw [cyclic_offset_normalized,sub_eq_zero]

/-- The next occupied raw offset wraps exactly the current fixed positions.
This gives exact height and exchange changes for the original permutation,
including phases which are not globally minimal. -/
theorem next_occupied_phase_with_order (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      (∀ i : Fin n,0 < (cyclicOffset p a i).val → t ≤ (cyclicOffset p a i).val) ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  classical
  let F := fixedPositions (permutation p a)
  let S := Finset.univ.filter fun i => 0 < (cyclicOffset p a i).val
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hh
    have hmove : permutation p a i ≠ i := by
      have hlt := (mem_descendingPositions _ _).mp hi
      intro he
      rw [he] at hlt
      omega
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have hne : cyclicOffset p a i ≠ 0 := fun h => hmove ((offset_zero_iff_source_fixed p a i).mp h)
    exact Fin.pos_iff_ne_zero.mpr hne
  obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image S (fun i => (cyclicOffset p a i).val) hS
  let t := (cyclicOffset p a b).val
  have ht : 0 < t := (Finset.mem_filter.mp hb).2
  have htn : t < n := (cyclicOffset p a b).isLt
  have hbelow (i : Fin n) : (cyclicOffset p a i).val < t ↔ i ∈ F := by
    have hz : (cyclicOffset p a i).val=0 ↔ i ∈ F := by
      have hv : (cyclicOffset p a i).val=0 ↔ cyclicOffset p a i=0 := by
        constructor
        · exact fun h => Fin.ext h
        · exact fun h => congrArg Fin.val h
      rw [hv,offset_zero_iff_source_fixed]
      exact (mem_fixedPositions _ _).symm
    constructor
    · intro hi
      apply hz.mp
      by_contra hnot
      have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      have hbi := hbmin i him
      omega
    · intro hi
      rw [hz.mpr hi]
      exact ht
  have hcount : belowCount p a t=F.card := by
    unfold belowCount
    congr 1
    apply Finset.ext
    intro i
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hbelow i
  have hheight := reanchor_height p a b
  change (height p b : ℤ)=(height p a : ℤ)-(t : ℤ)+belowCount p a t at hheight
  rw [hcount] at hheight
  have hFle : F.card ≤ n := (Finset.card_le_univ F).trans_eq (Fintype.card_fin n)
  have hcard : Fᶜ.card=n-F.card := by rw [Finset.card_compl,Fintype.card_fin]
  have heq : displacement p b=phaseShift (displacement p a) Fᶜ := by
    funext i
    rw [displacement_offset,cyclic_offset_reanchor p a b i,cyclic_subtraction_value]
    unfold phaseShift
    rw [hcard,Nat.cast_sub hFle,displacement_offset]
    by_cases hi : i ∈ F
    · have hb := (hbelow i).mpr hi
      change (cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_true,Finset.mem_compl,hi,not_true_eq_false,ite_false]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+(n : ℤ))-(height p b : ℤ)=_
      omega
    · have hb : ¬(cyclicOffset p a i).val < t := fun hb => hi ((hbelow i).mp hb)
      change ¬(cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_false,Finset.mem_compl,hi,not_false_eq_true,ite_true]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+0)-(height p b : ℤ)=_
      omega
  have htop : ∀ i ∈ Fᶜ,∀ j ∉ Fᶜ,displacement p a j ≤ displacement p a i := by
    intro i _ j hj
    have hj' : j ∈ F := by simpa using hj
    rw [fixed_source_displacement p a j hj']
    have hb := (displacement_band p a i).1
    omega
  have hsum : (∑ i ∈ Fᶜ,displacement p a i)=(F.card : ℤ)*height p a := by
    have hFsum : (∑ i ∈ F,displacement p a i)= -((F.card : ℤ)*height p a) := by
      calc
        _ = ∑ _i ∈ F,-(height p a : ℤ) := Finset.sum_congr rfl
          (fun i hi => fixed_source_displacement p a i hi)
        _ = _ := by simp
    have hs := Finset.sum_compl_add_sum F (displacement p a)
    rw [hFsum,displacement_balance] at hs
    omega
  have hI := top_phase_inversions (is_lift p a) Fᶜ (displacement_strict_width p a) htop
  rw [← heq,hcard,Nat.cast_sub hFle,hsum] at hI
  refine ⟨b,t,ht,htn,?_,?_,by change _=_+(F.card : ℤ)-_; omega,?_⟩
  · intro i hi
    exact hbmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  · have ho : cyclicOffset p a b=(t : Fin n) := by simp [t]
    unfold cyclicOffset at ho
    linear_combination ho
  · change _=(F.card : ℤ)*_
    nlinarith

theorem next_occupied_phase (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  obtain ⟨b,t,ht,htn,_,hoff,hhb,hI⟩ := next_occupied_phase_with_order p a hh
  exact ⟨b,t,ht,htn,hoff,hhb,hI⟩


#print axioms next_occupied_phase


end LX.AnchoredPhases
