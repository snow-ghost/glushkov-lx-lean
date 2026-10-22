import LX.ShortWindowQuadraticUpper

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A later equal-height phase forces the earlier fixed fiber to fit
inside their separation. This controls every phase except the least gap. -/
theorem smaller_gap_bounds_fixed (p : State n) (a b : Fin n)
    (hh : height p b=height p a) (hg : (b-p b).val < (a-p a).val) :
    (fixedPositions (permutation p a)).card ≤ (a-p a).val := by
  have hoff : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    rw [hoff,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hg.le)]
  have he := reanchor_height p a b
  have hcount : belowCount p a (cyclicOffset p a b).val=(cyclicOffset p a b).val := by omega
  have hf : (fixedPositions (permutation p a)).card ≤ belowCount p a (cyclicOffset p a b).val := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p a i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  omega

/-- The largest forward difference belongs to position zero, so it must
not be counted again among the non-head exceptions. -/
theorem complete_good_anchor_four (p : State n) (hp : CompleteMapping p) (h : ℕ)
    (hn : n=2*h+1) (hh : 5 ≤ h) :
    ∃ a : Fin n, 0 < a.val ∧ a.val+h ≤ (p a).val+4 ∧
      5 ≤ a.val+(n-(p a).val) := by
  let P := Finset.univ.filter (fun i : Fin n => i.val < (p i).val)
  let δ := fun i : Fin n => (p i).val-i.val
  have hcard : P.card=h := complete_positive_count p hp h hn
  have hinj : Set.InjOn δ P := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply hp
    have hcast := congrArg (fun k : ℕ => (k : Fin n)) he
    simpa only [δ,Nat.cast_sub (Nat.le_of_lt hi'),Nat.cast_sub (Nat.le_of_lt hj'),
      Fin.cast_val_eq_self] using hcast
  by_contra hnone
  push Not at hnone
  let S : Finset ℕ := (Finset.Icc 1 (h-5) ∪ Finset.Icc (n-4) (n-2)) ∪ {δ 0}
  have hsub : P.image δ ⊆ S := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hpa := (Finset.mem_filter.mp ha).2
    have hpn := (p a).isLt
    by_cases ha0 : a=0
    · subst a
      simp [S]
    · have hap : 0 < a.val := Fin.pos_iff_ne_zero.mpr ha0
      by_cases hlo : δ a ≤ h-5
      · have hδpos : 0 < δ a := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inl ⟨hδpos,hlo⟩)
      · have hforward : a.val+h ≤ (p a).val+4 := by dsimp [δ] at hlo; omega
        have hnot := hnone a hap hforward
        have hδhi : n-4 ≤ δ a ∧ δ a ≤ n-2 := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inr hδhi)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,hcard] at hc
  have hcu := Finset.card_union_le (Finset.Icc 1 (h-5) ∪ Finset.Icc (n-4) (n-2)) {δ 0}
  have hcu' := Finset.card_union_le (Finset.Icc 1 (h-5)) (Finset.Icc (n-4) (n-2))
  change S.card ≤ _ at hcu
  simp only [Nat.card_Icc,Finset.card_singleton] at hcu hcu'
  omega

theorem complete_mapping_fourteen_word (p : State n) (hp : CompleteMapping p) (hn : 4 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14 := by
  by_cases hsmall : n < 11
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn p⁻¹
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hn' : (n : ℤ) ≤ 9 := by have := complete_height p hp 0; omega
    linarith
  · let h := height p 0
    have hparity : n=2*h+1 := complete_height p hp 0
    obtain ⟨a,ha,hforward,hcorner⟩ := complete_good_anchor_four p hp h hparity (by omega)
    have hheight : height p a=h := by have := complete_height p hp a; omega
    obtain ⟨w,hw,hprice⟩ := odd_forward_anchor_word p a 4 (complete_majorized p hp a)
      (by omega) (by omega) ha (by omega) hcorner
    exact ⟨w,hw,by omega⟩

/-- Source selection at constant fourteen, independent of the older
constant-thirty-two reductions. -/
theorem fourteen_unpaid_minimum (hn4 : 4 ≤ n) (p : State n) (m e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      ∀ b,height p a ≤ height p b := by
  have hlower (b : Fin n) : m ≤ height p b+1 := by
    by_contra hnot
    interval_cases e
    · by_cases hb : height p b+2=m
      · obtain ⟨w,hw,hprice⟩ := even_second_height_four_word p b (by omega)
        exact hunpaid ⟨w,hw,by linarith⟩
      · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
        exact hunpaid ⟨w,hw,by linarith⟩
    · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
      exact hunpaid ⟨w,hw,by linarith⟩
  have hex : ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m := by
    interval_cases e
    · obtain ⟨a,ha⟩ := exists_global_minimum p
      have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
      rw [displacement_anchor] at hh
      exact ⟨a,ha,by have := hlower a; omega⟩
    · by_contra hnone
      have hheight (a : Fin n) (ha : GlobalMinimum p a) : height p a=m := by
        have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
        rw [displacement_anchor] at hh
        have hne : height p a+1 ≠ m := fun hh => hnone ⟨a,ha,hh⟩
        have := hlower a
        omega
      exact hunpaid (complete_mapping_fourteen_word p (odd_maximal_minima_complete p m hn hheight) hn4)
  obtain ⟨a,ha,hh⟩ := hex
  exact ⟨a,ha,hh,fun b => by have := hlower b; omega⟩

#print axioms smaller_gap_bounds_fixed
#print axioms complete_good_anchor_four
#print axioms fourteen_unpaid_minimum
end LX.AnchoredPhases
