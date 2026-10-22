import LX.OddLowerPhaseLocations

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem height_zero_source_fixed (p : State n) (a : Fin n)
    (hh : height p a=0) (i : Fin n) : permutation p a i=i := by
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => (cyclicOffset p a j : ℤ))
    (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  rw [cyclic_offset_mass,hh,Nat.cast_zero,mul_zero] at hs
  have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  exact (offset_zero_iff_source_fixed p a i).mp hz

/-- If every global minimum saturates its fixed-position bound, the next
occupied offset is also global. A nearest-predecessor argument then reaches
every actual anchor, without assuming a uniform height or an orbit length. -/
theorem all_anchors_global_of_saturated_minima (p : State n)
    (hsat : ∀ a : Fin n,GlobalMinimum p a →
      (fixedPositions (permutation p a)).card=n-2*height p a) :
    ∀ c : Fin n,GlobalMinimum p c := by
  classical
  intro c
  let G := Finset.univ.filter (GlobalMinimum p)
  have hG : G.Nonempty := by
    obtain ⟨a,ha⟩ := exists_global_minimum p
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image G (fun a => (cyclicOffset p a c).val) hG
  have ha' : GlobalMinimum p a := (Finset.mem_filter.mp ha).2
  by_cases hz : cyclicOffset p a c=0
  · apply same_offset_global_minimum ha'
    exact sub_eq_zero.mp hz
  · have hpos : 0 < (cyclicOffset p a c).val := Fin.pos_iff_ne_zero.mpr hz
    have hh : 0 < height p a := by
      by_contra hnot
      have hfix := height_zero_source_fixed p a (by omega) c
      exact hz ((offset_zero_iff_source_fixed p a c).mpr hfix)
    obtain ⟨b,t,ht,htn,htmin,hoff,_,hI⟩ := next_occupied_phase_with_order p a hh
    have hf := hsat a ha'
    have hfpos : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
      ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
    have hbalance : (n : ℤ)-2*height p a-(fixedPositions (permutation p a)).card=0 := by omega
    rw [hbalance,mul_zero] at hI
    have hIb : inversions (displacement p b)=inversions (displacement p a) := by omega
    have hb : GlobalMinimum p b := global_minimum_of_equal_exchanges ha' hIb
    have hnear := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
    have htle := htmin c hpos
    have ho : cyclicOffset p a b=(t : Fin n) := by
      unfold cyclicOffset
      rw [hoff]
      ring
    have htv : (t : Fin n).val=t := by simp [Nat.mod_eq_of_lt htn]
    have hle : (t : Fin n) ≤ cyclicOffset p a c := by change (t : Fin n).val ≤ _; rwa [htv]
    have hv : (cyclicOffset p b c).val=(cyclicOffset p a c).val-t := by
      rw [cyclic_offset_reanchor p a b c,ho,Fin.coe_sub_iff_le.mpr hle,htv]
    omega

/-- Conversely, if every anchor is global, each occupied phase transition
has zero exchange change, forcing saturation of the fixed-position bound. -/
theorem saturated_of_all_anchors_global (p : State n)
    (hall : ∀ a : Fin n,GlobalMinimum p a) (a : Fin n) :
    (fixedPositions (permutation p a)).card=n-2*height p a := by
  classical
  by_cases hh : height p a=0
  · have he : fixedPositions (permutation p a)=Finset.univ := by
      apply Finset.ext
      intro i
      simp only [mem_fixedPositions,Finset.mem_univ,iff_true]
      exact height_zero_source_fixed p a hh i
    rw [he,Finset.card_univ,Fintype.card_fin,hh]
    omega
  · obtain ⟨b,_,_,_,_,_,hI⟩ := next_occupied_phase p a (by omega)
    have he : inversions (displacement p b)=inversions (displacement p a) :=
      Nat.le_antisymm (global_minimum_exchanges (hall b) a) (global_minimum_exchanges (hall a) b)
    rw [he,sub_self] at hI
    have hfpos : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
      ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
    have hfne : ((fixedPositions (permutation p a)).card : ℤ) ≠ 0 := by omega
    have hz := (mul_eq_zero.mp hI.symm).resolve_left hfne
    omega

theorem saturated_minima_iff_all_anchors_global (p : State n) :
    (∀ a : Fin n,GlobalMinimum p a →
      (fixedPositions (permutation p a)).card=n-2*height p a) ↔
      ∀ a : Fin n,GlobalMinimum p a := by
  exact ⟨all_anchors_global_of_saturated_minima p,
    fun hall a _ => saturated_of_all_anchors_global p hall a⟩

/-- The unpaid odd branch either has a lower global source with one or two
fixed positions, or every anchor is global. The three-fixed alternative is
therefore accompanied by a proved global closure property. -/
theorem odd_unpaid_small_fixed_or_all_global (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card ≤ 2) ∨
      (∀ a : Fin n,GlobalMinimum p a) := by
  by_cases hex : ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card ≤ 2
  · exact Or.inl hex
  · right
    apply all_anchors_global_of_saturated_minima p
    intro a ha
    have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
    rw [displacement_anchor] at hh
    by_cases hhigh : height p a=m
    · have hf := odd_higher_fixed_unique p a (global_minimum_majorized ha) (by omega)
      omega
    · have hlow : height p a+1=m := by
        by_contra hnot
        obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a (by omega)
        exact hunpaid ⟨w,hw,by linarith⟩
      have hf := majorized_anchor_fixed_positions p a (global_minimum_majorized ha)
      have hnot : ¬ (fixedPositions (permutation p a)).card ≤ 2 := fun h => hex ⟨a,ha,hlow,h⟩
      omega

#print axioms all_anchors_global_of_saturated_minima
#print axioms saturated_of_all_anchors_global
#print axioms saturated_minima_iff_all_anchors_global
#print axioms odd_unpaid_small_fixed_or_all_global
end LX.AnchoredPhases
