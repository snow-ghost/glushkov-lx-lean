import LRX.JoinedPositiveArcCases

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem ordered_joined_cursor_cases (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (s t : Fin n) (hst : s.val ≤ t.val) :
    (s.val < t.val ∧ JoinedPositiveArcs p hc s t ∧ JoinedPositiveArcs p hc t s) ∨
      SourceCursorGap p s t ∨ OuterCursorPair p hc s t := by
  classical
  let L := outerLeft p hc
  let R := outerRight p hc
  obtain ⟨hLR,hL,hR,hloadL,hloadR⟩ := joined_outer_ports hn p hc hk
  change L.val < R.val at hLR
  change L ∈ sourcePackets p at hL
  change R ∈ sourcePackets p at hR
  have hR0 : R ≠ 0 := by intro h; rw [h,Fin.val_zero] at hLR; omega
  have hpred : (R-1 : Fin n).val=R.val-1 := Fin.val_sub_one_of_ne_zero hR0
  have hposL : 0 < portLoad (displacement (joinedComponents p hc).symm) L := by
    change 2 ≤ portLoad (displacement (joinedComponents p hc).symm) L at hloadL
    omega
  have hposR : 0 < portLoad (displacement (joinedComponents p hc).symm) (R-1) := by
    change 2 ≤ portLoad (displacement (joinedComponents p hc).symm) (R-1) at hloadR
    omega
  by_cases hs : L.val ≤ s.val ∧ s.val < R.val
  · by_cases ht : L.val ≤ t.val ∧ t.val < R.val
    · by_cases hm : ∃ z ∈ sourcePackets p, s.val < z.val ∧ z.val ≤ t.val
      · obtain ⟨z,hz,hsz,hzt⟩ := hm
        have hst' : s.val < t.val := by omega
        have hzpos := joined_load_positive_between hn p hc hk z (by change L.val ≤ z.val; omega)
          (by change z.val < R.val; omega)
        have hb := positive_arcs_from_between_outside p hc s t hst' z z L L hz hL
          (Or.inl rfl) (Or.inl rfl) ⟨by omega,hzt⟩ (Or.inl hs.1) hzpos hposL
        exact Or.inl ⟨hst',hb⟩
      · right; left
        exact finite_marked_gap (sourcePackets p) L R s t hL hR hs.1 hs.2 hst
          (fun z hz h => hm ⟨z,hz,h⟩)
    · have htR : R.val ≤ t.val := by omega
      have hst' : s.val < t.val := by omega
      have hb := positive_arcs_from_between_outside p hc s t hst' R (R-1) L L hR hL
        (Or.inr (by ring)) (Or.inl rfl) ⟨by rw [hpred]; omega,by rw [hpred]; omega⟩
        (Or.inl hs.1) hposR hposL
      exact Or.inl ⟨hst',hb⟩
  · by_cases ht : L.val ≤ t.val ∧ t.val < R.val
    · have hsL : s.val < L.val := by omega
      have hst' : s.val < t.val := by omega
      have hb := positive_arcs_from_between_outside p hc s t hst' L L R (R-1) hL hR
        (Or.inl rfl) (Or.inr (by ring)) ⟨by omega,ht.1⟩
        (Or.inr (by rw [hpred]; omega)) hposL hposR
      exact Or.inl ⟨hst',hb⟩
    · right; right
      change (R.val ≤ s.val ∨ s.val < L.val) ∧ (R.val ≤ t.val ∨ t.val < L.val)
      constructor <;> omega

theorem joined_cursor_cases (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (start finish : Fin n) :
    (start ≠ finish ∧ JoinedPositiveArcs p hc start finish) ∨
      SourceCursorGap p start finish ∨ OuterCursorPair p hc start finish := by
  by_cases h : start.val ≤ finish.val
  · rcases ordered_joined_cursor_cases hn p hc hk start finish h with h | h
    · exact Or.inl ⟨fun he => by have hh := congrArg Fin.val he; omega,h.2.1⟩
    · exact Or.inr h
  · rcases ordered_joined_cursor_cases hn p hc hk finish start (by omega) with h | h | h
    · exact Or.inl ⟨fun he => by have hh := congrArg Fin.val he; omega,h.2.2⟩
    · obtain ⟨u,hu,v,hv,huv,hgap,huf,hfv,hus,hsv⟩ := h
      exact Or.inr (Or.inl ⟨u,hu,v,hv,huv,hgap,hus,hsv,huf,hfv⟩)
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)

#print axioms joined_cursor_cases
end LRX.FiniteCuts
