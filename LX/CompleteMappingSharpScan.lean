import LX.FiberDepthGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem complete_good_anchor_two (p : State n) (hp : CompleteMapping p) (h : ℕ)
    (hn : n=2*h+1) (hh : 3 ≤ h) :
    ∃ a : Fin n, 0 < a.val ∧ a.val+h ≤ (p a).val+2 ∧
      3 ≤ a.val+(n-(p a).val) := by
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
  let T := Finset.Icc (n-2) (n-2)
  have hTcard : T.card ≤ 1 := by simp [T]
  let S : Finset ℕ := (Finset.Icc 1 (h-3) ∪ T) ∪ {δ 0}
  have hsub : P.image δ ⊆ S := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hpa := (Finset.mem_filter.mp ha).2
    have hpn := (p a).isLt
    by_cases ha0 : a=0
    · subst a
      simp [S]
    · have hap : 0 < a.val := Fin.pos_iff_ne_zero.mpr ha0
      by_cases hlo : δ a ≤ h-3
      · have hδpos : 0 < δ a := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inl ⟨hδpos,hlo⟩)
      · have hforward : a.val+h ≤ (p a).val+2 := by dsimp [δ] at hlo; omega
        have hnot := hnone a hap hforward
        have hδhi : n-2 ≤ δ a ∧ δ a ≤ n-2 := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        apply Or.inl
        apply Or.inr
        exact Finset.mem_Icc.mpr hδhi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,hcard] at hc
  have hcu := Finset.card_union_le (Finset.Icc 1 (h-3) ∪ T) {δ 0}
  have hcu' := Finset.card_union_le (Finset.Icc 1 (h-3)) T
  change S.card ≤ _ at hcu
  simp only [Nat.card_Icc,Finset.card_singleton] at hcu hcu'
  omega

/-- Complete mappings use the constant-height next-depth bound three. -/
theorem complete_mapping_sharp_scan_word (p : State n) (hp : CompleteMapping p)
    (hn : 7 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+13 := by
  let h := height p 0
  have hparity : n=2*h+1 := complete_height p hp 0
  have hall (a : Fin n) : height p a=h := by
    have := complete_height p hp a
    omega
  have hfixed (a : Fin n) : (fixedPositions (permutation p a)).card=1 :=
    odd_higher_fixed_unique p a (complete_majorized p hp a) (complete_height p hp a)
  obtain ⟨a,ha,hforward,hcorner⟩ := complete_good_anchor_two p hp h hparity (by omega)
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hz := one_fixed_last_offset p a (hfixed a) 0 (by simpa using he)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hv
    omega
  have hlast (i : Fin n) (hi : p i-i=p a-a) : i.val ≤ a.val := by
    rw [one_fixed_last_offset p a (hfixed a) i hi]
  have hne : p a ≠ 0 := by
    intro he
    rw [he,Fin.val_zero] at hforward
    omega
  have hneg : (-p a).val=n-(p a).val := by simp [Fin.val_neg,hne]
  have hc := constant_height_next_depth p h 1 hall (fun b => (hfixed b).le) (by omega) a
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by
    rw [hall a,hneg]
    omega
  obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p a (by omega)
    (complete_height p hp a) hhead hlast hcount
  have hr := anchor_reserve_nonneg p a
  rw [hneg,hall a] at hprice
  exact ⟨w,hw,by omega⟩

theorem complete_mapping_eight_word (p : State n) (hp : CompleteMapping p) (hn : 4 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8 := by
  by_cases hlarge : 7 ≤ n
  · obtain ⟨w,hw,hprice⟩ := complete_mapping_sharp_scan_word p hp hlarge
    exact ⟨w,hw,by omega⟩
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn p⁻¹
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hn' : (n : ℤ) ≤ 5 := by have := complete_height p hp 0; omega
    linarith

#print axioms complete_good_anchor_two
#print axioms complete_mapping_sharp_scan_word
#print axioms complete_mapping_eight_word
end LX.AnchoredPhases
