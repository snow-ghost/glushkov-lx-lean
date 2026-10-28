import LX.AllGlobalOddGeometry
import LX.EvenSecondFewFixed
import LX.NearMinimumPhases
import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- With constant anchor height, a cumulative offset count overshoots its
threshold by less than the largest fixed fiber. -/
theorem constant_height_below_count (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (a : Fin n) (t : ℕ) (ht : 0 < t) :
    belowCount p a t ≤ t+F-1 := by
  classical
  let S := Finset.univ.filter fun i => (cyclicOffset p a i).val < t
  have hS : S.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    simpa only [cyclicOffset,sub_self,Fin.val_zero] using ht⟩⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S (fun i => (cyclicOffset p a i).val) hS
  let U := Finset.univ.filter fun i => (cyclicOffset p a i).val < (cyclicOffset p a b).val
  let V := fixedPositions (permutation p b)
  have hsub : S ⊆ U ∪ V := by
    intro i hi
    have hle := hmax i hi
    by_cases hlt : (cyclicOffset p a i).val < (cyclicOffset p a b).val
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩)
    · apply Finset.mem_union_right
      apply (mem_fixedPositions _ _).mpr
      apply (offset_zero_iff_source_fixed p b i).mp
      rw [cyclic_offset_reanchor p a b i]
      have he : cyclicOffset p a i=cyclicOffset p a b := Fin.ext (by omega)
      rw [he,sub_self]
  have hU : U.card=(cyclicOffset p a b).val := by
    have hh := reanchor_height p a b
    rw [hall a,hall b] at hh
    change U.card=_
    change (h : ℤ)=(h : ℤ)-(cyclicOffset p a b : ℤ)+U.card at hh
    omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  have hV := hF b
  have hb' := (Finset.mem_filter.mp hb).2
  change V.card ≤ F at hV
  change S.card ≤ _
  omega

/-- The next-depth count is bounded uniformly by the largest fixed fiber,
without any majorization or exchange-reserve assumption. -/
theorem constant_height_next_depth (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 0 < h) (a : Fin n) :
    depthCount (displacement p a) (h-1) ≤ 2*F+1 := by
  classical
  have htop : depthCount (displacement p a) h ≤ F := by
    rw [← hall a,top_depth_count_eq_fixed]
    exact hF a
  have hsub : Finset.univ.filter (fun i => h-1 ≤ backwardDepth (displacement p a) i) ⊆
      Finset.univ.filter (fun i => (cyclicOffset p a i).val < F+2) := by
    intro i hi
    have hdepth := (Finset.mem_filter.mp hi).2
    have hw := displacement_depth_width_bound (is_lift p a)
      (fun i j => (displacement_strict_width p a i j).le) (h-1) i hdepth
    rw [show h-1+1=h by omega,displacement_offset,hall a] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have hc := Finset.card_le_card hsub
  have hb := constant_height_below_count p h F hall hF a (F+2) (by omega)
  change depthCount (displacement p a) (h-1) ≤ belowCount p a (F+2) at hc
  omega

/-- The actual ordinary backward arrows are counted using a maximal raw
offset. Constant height suffices; global energy minimality is not required. -/
theorem constant_height_descending_bound (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hn : n=2*h+2) :
    (descendingPositions p).card ≤ h+F-1 := by
  classical
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => (p i-i).val) ⟨0,Finset.mem_univ _⟩
  let A := fixedPositions (permutation p a)
  have hAl : A.card ≤ n := (Finset.card_le_univ A).trans_eq (Fintype.card_fin n)
  have hfilter : Finset.univ.filter (fun i : Fin n => (p i-i).val < (p a-a).val)=Aᶜ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    have hm := hmax i (Finset.mem_univ _)
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
  rw [hif,hall a] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hnpos : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hid : ((descendingPositions p).card : ℤ)=(h : ℤ)+(p a-a).val-n+A.card := by
    nlinarith
  have hfa := hF a
  change A.card ≤ F at hfa
  have hr := (p a-a).isLt
  omega

/-- Every residue has an occupied predecessor less than F steps away.
All intervening gaps are derived from actual equal-height phases. -/
theorem constant_height_predecessor (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 0 < h) (r : Fin n) :
    ∃ a : Fin n,(r-(p a-a)).val < F := by
  obtain ⟨a,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun a => (r-(p a-a)).val) ⟨0,Finset.mem_univ _⟩
  refine ⟨a,?_⟩
  by_contra hnot
  obtain ⟨b,t,ht,htn,hoff,hheight,_⟩ := next_occupied_phase p a (by rw [hall a]; exact hh)
  rw [hall a,hall b] at hheight
  have htf : t ≤ F := by have := hF a; omega
  have htv : (t : Fin n).val=t := by simp [Nat.mod_eq_of_lt htn]
  have hle : (t : Fin n) ≤ r-(p a-a) := by change (t : Fin n).val ≤ _; rw [htv]; omega
  have he : r-(p b-b)=r-(p a-a)-(t : Fin n) := by rw [hoff]; ring
  have hnear := hmin b (Finset.mem_univ _)
  rw [he,Fin.coe_sub_iff_le.mpr hle,htv] at hnear
  omega

#print axioms constant_height_below_count
#print axioms constant_height_next_depth
#print axioms constant_height_descending_bound
#print axioms constant_height_predecessor
end LX.AnchoredPhases
