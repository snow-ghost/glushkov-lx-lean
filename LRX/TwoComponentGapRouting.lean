import LRX.TwoComponentPositiveGap

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem two_component_original_positive_gap_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=1)
    (u v : Fin n) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u)
    (start finish : Fin n) (hs : u.val ≤ start.val ∧ start.val < v.val)
    (hf : u.val ≤ finish.val ∧ finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hcan := component_cut_canonical_displacement p root
  have hsource (x : Fin n) : x-r ∈ sourcePackets q ↔ x ∈ sourcePackets p := by
    have h := source_packets_recenter p r hcan (x-r)
    simpa only [RotationWords.rotation,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,sub_add_cancel] using h
  have hinterval := interval_recenter_outside u v r huv
    (positive_source_gap_cut_outside p root u v hu hv huv hgap hpos)
  have hu' := (hsource u).mpr hu
  have hv' := (hsource v).mpr hv
  have hgap' (x : Fin n) (hux : (u-r).val < x.val) (hxv : x.val < (v-r).val) :
      x ∉ sourcePackets q := by
    have hx := (hinterval.2.2 (x+r)).mpr (by simpa only [add_sub_cancel_right] using And.intro hux hxv)
    intro hxs
    apply hgap (x+r) hx.1 hx.2
    exact (hsource (x+r)).mp (by simpa only [add_sub_cancel_right] using hxs)
  have hpos' : 0 < portLoad (displacement q.symm) (u-r) := by
    rw [← hcan,port_load_recenter,sub_add_cancel]
    exact hpos
  obtain ⟨hnext,hselected⟩ := consecutive_positive_gap_selected q n (u-r) (v-r)
    hu' hv' hinterval.1 hgap' hpos' (v-r).isLt.le
  have hs' := (hinterval.2.1 start).mp hs
  have hf' := (hinterval.2.1 finish).mp hf
  apply two_component_internal_gap_sharp_word hn p hmaj hm root hlarge ht
    ⟨u-r,hselected⟩ start finish hs'.1 ?_ hf'.1 ?_
  · change (start-r).val < FiniteGaps.next (sourcePackets q) (u-r)
    simpa only [hnext] using hs'.2
  · change (finish-r).val < FiniteGaps.next (sourcePackets q) (u-r)
    simpa only [hnext] using hf'.2


/-- The actual zero-gap price is paid by C7 also when t=1. -/
theorem two_component_isolated_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let delta := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)
    1 ≤ delta ∧ 3*((isolatedVertices p).card : ℤ) ≤ delta := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  have hcount := component_cut_external_count p root (by omega)
  have ht : (nontrivialSuffixComponents q L).card=1 := by
    change (nontrivialSuffixComponents q L).card+1=(componentRoots p).card at hcount
    omega
  have hreserve := large_component_numeric_reserve hn p hmaj (by omega) root hlarge
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    2*(((nontrivialSuffixComponents q L).card : ℤ)-1)*
      ((v : ℤ)-((nontrivialSuffixComponents q L).card : ℤ))+
    (a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤ _ at hreserve
  rw [ht] at hreserve
  norm_num only [Nat.cast_one,sub_self,mul_zero,zero_mul,add_zero] at hreserve
  have hv : 2 ≤ v := by
    have h := nontrivial_suffix_size_sum q L
    rw [ht] at h
    exact h
  have hprod := mul_nonneg (show (0 : ℤ) ≤ a by positivity)
    (show (0 : ℤ) ≤ (v : ℤ)-2 by omega)
  have hpair : (a : ℤ) ≤ (a.choose 2 : ℤ)+1 := by
    have h := twice_choose_two_int a
    by_cases ha : a ≤ 1
    · interval_cases a <;> norm_num
    · have hh := mul_nonneg (show (0 : ℤ) ≤ (a : ℤ)-1 by omega)
        (show (0 : ℤ) ≤ (a : ℤ)-2 by omega)
      nlinarith
  have hnonneg : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hiso : a=(isolatedVertices p).card := component_cut_singleton_count p root (by omega)
  have hi : ((isolatedVertices p).card : ℤ)=(a : ℤ) := by exact_mod_cast hiso.symm
  dsimp only
  rw [hi]
  have hpairs : (0 : ℤ) ≤ (a.choose 2 : ℤ) := by positivity
  have ha : (0 : ℤ) ≤ a := by positivity
  constructor <;> nlinarith

theorem two_component_original_zero_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card-2 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  have hres := (two_component_isolated_reserve hn p hmaj hc root hlarge).2
  have hB := component_bridge_isolated_budget p hc
  omega

/-- Every original source gap, positive or zero, is sharp for two nontrivial
components. No maximal cut or positive packet-defect premise is required. -/
theorem two_component_source_gap_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (u v : Fin n) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (start finish : Fin n) (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hpos : 0 < portLoad (displacement p.symm) u
  · have hcount := component_cut_external_count p root (by omega)
    have ht : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card=1 := by omega
    exact two_component_original_positive_gap_word hn p hmaj (by omega) root hlarge ht
      u v hu hv huv hgap hpos start finish ⟨hsu,hsv⟩ ⟨hfu,hfv⟩
  · have hz : portLoad (displacement p.symm) u=0 := by
      have := port_load_nonneg (displacement p.symm) u
      omega
    obtain ⟨f,w,hmatch,he,hl⟩ := joined_source_gap_min_word (by omega) p hc (by omega)
      u v huv hu hv hgap start finish hsu hsv hfu hfv
    have hw := zero_source_gap_isolated_width p u v hgap hz
    have hwidth : (v.val : ℤ)-(u.val : ℤ) ≤ ((isolatedVertices p).card : ℤ)+1 := by omega
    have hmin : min ((gapCost f : ℤ)-portLoad (displacement p.symm) u)
        ((v.val : ℤ)-(u.val : ℤ)-3) ≤ ((v.val : ℤ)-(u.val : ℤ)-3) := min_le_right _ _
    have hreserve := two_component_original_zero_reserve (by omega) p hmaj hc root hlarge
    have hmass := majorized_canonical_energy p hmaj
    have hchoose := choose_two_half_identity n
    have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
    exact ⟨w,he,by exact_mod_cast hlen⟩

/-- Two-component routing now has only the exterior-gap and peak cases left. -/
theorem two_component_sharp_or_peak_or_outer (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      ((start ≠ finish ∧ JoinedPositiveArcs p hc start finish) ∨ OuterCursorPair p hc start finish) := by
  rcases joined_cursor_cases (by omega) p hc (by omega) start finish with h | h | h
  · exact Or.inr (Or.inl h)
  · obtain ⟨u,hu,v,hv,huv,hgap,hsu,hsv,hfu,hfv⟩ := h
    exact Or.inl (two_component_source_gap_sharp_word hn p hmaj hc root hlarge
      u v hu hv huv hgap start finish hsu hsv hfu hfv)
  · exact Or.inr (Or.inr h)

#print axioms two_component_original_positive_gap_word
#print axioms two_component_original_zero_reserve
#print axioms two_component_source_gap_sharp_word
#print axioms two_component_sharp_or_peak_or_outer
end LRX.FiniteCuts
