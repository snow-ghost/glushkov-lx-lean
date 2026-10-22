import LRX.IsolatedGapSharpPayment
import LRX.JoinedSourceGapMinimum

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem nonzero_component_left_source (p : State n) (a : Fin n)
    (hc : 2 ≤ (componentSet p a).card) (hl : componentLeft p a ≠ 0) :
    componentLeft p a ∈ sourcePackets p := by
  let l := componentLeft p a
  have hm : p.symm l ≠ l := nontrivial_component_left_moved p a hc
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hadj : CycleFootprint.Adjacent l (l-1) := Or.inr (by ring)
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) l (l-1) := by
    intro hp
    have hb := component_left_bound p a (l-1) ((component_left_path p a).trans hp)
    change l.val ≤ (l-1 : Fin n).val at hb
    rw [Fin.val_sub_one_of_ne_zero hl] at hb
    have hv := Fin.val_ne_zero_iff.mpr hl
    change l.val ≠ 0 at hv
    omega
  apply component_universal_source p l hm
  intro x hx hp
  exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm)
    ⟨l,hm⟩ (l-1) hadj hout ⟨x,hx⟩ hp

/-- A source-free interval following a zero port contains only singleton components. -/
theorem zero_source_gap_singleton (p : State n) (u v : Fin n)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hz : portLoad (displacement p.symm) u = 0)
    (x : Fin n) (hux : u.val < x.val) (hxv : x.val < v.val) :
    (componentSet p x).card = 1 := by
  have hcpos := Finset.card_pos.mpr (component_set_nonempty p x)
  by_contra hh
  have hc : 2 ≤ (componentSet p x).card := by omega
  let l := componentLeft p x
  have hs := zero_port_path_side p u hz (component_left_path p x)
  have hlo : u.val < l.val := by change x.val ≤ u.val ↔ l.val ≤ u.val at hs; omega
  have hlx : l.val ≤ x.val := component_left_bound p x x Relation.ReflTransGen.refl
  have hl0 : componentLeft p x ≠ 0 := by intro he; change u.val < (componentLeft p x).val at hlo; rw [he,Fin.val_zero] at hlo; omega
  exact hgap l hlo (by omega) (nonzero_component_left_source p x hc hl0)

theorem zero_source_gap_isolated_width (p : State n) (u v : Fin n)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hz : portLoad (displacement p.symm) u = 0) :
    v.val-u.val ≤ (isolatedVertices p).card+1 := by
  classical
  have hsub : Finset.Ioo u v ⊆ isolatedVertices p := by
    intro x hx
    obtain ⟨hux,hxv⟩ := Finset.mem_Ioo.mp hx
    exact (mem_isolated_vertices p x).mpr (zero_source_gap_singleton p u v hgap hz x hux hxv)
  have h := Finset.card_le_card hsub
  rw [Fin.card_Ioo] at h
  omega

/-- Sharp payment for the zero-load case of the general source-gap certificate. -/
theorem joined_zero_source_gap_sharp_word (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (hreserve : 2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hz : portLoad (displacement p.symm) u = 0) (start finish : Fin n)
    (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨f,w,hmatch,he,hl⟩ := joined_source_gap_min_word hn p hc hk u v huv hu hv hgap
    start finish hsu hsv hfu hfv
  have hw := zero_source_gap_isolated_width p u v hgap hz
  have hwidth : (v.val : ℤ)-(u.val : ℤ) ≤ ((isolatedVertices p).card : ℤ)+1 := by omega
  have hmin : min ((gapCost f : ℤ)-portLoad (displacement p.symm) u) ((v.val : ℤ)-(u.val : ℤ)-3) ≤
      (v.val : ℤ)-(u.val : ℤ)-3 := min_le_right _ _
  have hmass := majorized_canonical_energy p hmaj
  have hchoose := choose_two_half_identity n
  have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
  exact ⟨w,he,by exact_mod_cast hlen⟩

#print axioms zero_source_gap_singleton
#print axioms joined_zero_source_gap_sharp_word
end LRX.FiniteCuts
