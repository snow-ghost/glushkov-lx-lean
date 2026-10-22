import LRX.ComponentDensityBound

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The original source core of a large proper initial component has at least four vertices. -/
theorem large_prefix_source_core_card (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) : 4 ≤ (prefixSourceCore p).card := by
  classical
  have hn := NeZero.pos n
  have hc : 2 ≤ (componentSet p 0).card := by omega
  obtain ⟨hzero,hright,hw⟩ := prefix_component_source_ends p hc hproper
  let r := componentRight p 0
  have h0 : (0 : Fin n) ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hzero,by change 0 < (componentSet p 0).card; omega⟩
  have hr : r ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hright,by dsimp [r]; omega⟩
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hclosed (i : Fin n) (hi : i ∈ prefixSourceCore p) : p.symm i ∈ prefixSourceCore p := by
    obtain ⟨hs,hprefix⟩ := Finset.mem_filter.mp hi
    have hsi : p.symm i ∈ sourcePackets p :=
      (source_packets_invariant p (p.symm i)).mp (by simpa only [Equiv.apply_symm_apply] using hs)
    have hp := (CycleFootprint.mem_component _ _ _).mp ((zero_component_prefix p i).mpr hprefix)
    have hpi : p.symm i ∈ componentSet p 0 := (CycleFootprint.mem_component _ _ _).mpr
      (hp.trans (CycleFootprint.arrow_target_load_path hd i))
    exact Finset.mem_filter.mpr ⟨hsi,(zero_component_prefix p _).mp hpi⟩
  have h0r : (0 : Fin n) ≠ r := by
    intro he
    have hh := congrArg Fin.val he
    change 0 = (componentRight p 0).val at hh
    omega
  have hp0 : p.symm 0 ≠ 0 := ((mem_source_packets p 0).mp hzero).1
  have hpr : p.symm r ≠ r := ((mem_source_packets p r).mp hright).1
  have hshort := FiniteWindow.majorized_short (canonical_lift p.symm) hmaj
  have hp0r : p.symm 0 ≠ r := by
    intro he
    have hs := hshort 0
    have hab := le_abs_self (displacement p.symm 0)
    unfold displacement at hs hab
    rw [he] at hs hab
    change r.val+1 = (componentSet p 0).card at hw
    simp only [Fin.val_zero,Nat.cast_zero,sub_zero] at hs hab
    omega
  have hpr0 : p.symm r ≠ 0 := by
    intro he
    have hs := hshort r
    have hab := neg_le_abs (displacement p.symm r)
    unfold displacement at hs hab
    rw [he] at hs hab
    change r.val+1 = (componentSet p 0).card at hw
    simp only [Fin.val_zero,Nat.cast_zero,zero_sub,neg_neg] at hs hab
    omega
  have hpp : p.symm 0 ≠ p.symm r := fun h => h0r (p.symm.injective h)
  have hsub : ({0,r,p.symm 0,p.symm r} : Finset (Fin n)) ⊆ prefixSourceCore p := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact hr
    · exact hclosed 0 h0
    · exact hclosed r hr
  have hh := Finset.card_le_card hsub
  simpa [h0r,h0r.symm,hp0,hp0.symm,hpr,hpr.symm,hp0r,hp0r.symm,hpr0,hpr0.symm,hpp,hpp.symm] using hh

#print axioms large_prefix_source_core_card
end LRX.FiniteCuts
