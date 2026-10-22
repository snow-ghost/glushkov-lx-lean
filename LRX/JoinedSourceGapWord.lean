import LRX.SourceGapFilling

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The actual internal-gap word preserves the exact two-boundary profile of
its extracted original filling. It also applies to coincident cursors. -/
theorem joined_source_gap_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p)
    (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ v.val-u.val-1)
    (start finish : Fin n) (hpositions : (start.val=u.val+x ∧ finish.val=u.val+y) ∨
      (start.val=u.val+y ∧ finish.val=u.val+x)) :
    ∃ (filling : State (v.val-u.val-1)) (w : List Letter),
      (∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i)) ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-portLoad (displacement p.symm) u+
        min ((x : ℤ)+(y : ℤ)-cycleLeftLoad filling y)
          (2*((v.val-u.val-1 : ℕ) : ℤ)-(x : ℤ)-(y : ℤ)-cycleRightLoad filling x) := by
  obtain ⟨filling,hmatch,hout⟩ := source_gap_filling p u v huv hu hv hgap
  let G := joinedComponents p hc
  let W := sourceGapWindow u v huv
  have hGmatch (i) : G.symm (FiniteWindow.embed W i)=FiniteWindow.embed W (filling i) := by
    rw [joined_inverse_outside_packets p hc _ (hout i),hmatch]
  have hmov (r : Fin n) (hr : r ∈ sourcePackets p) : G.symm r ≠ r := by
    apply (mem_support_inverse _ r).mp
    change r ∈ (bridgeSequence p (componentBridges p hc)).support
    rw [bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)]
    exact (mem_support_inverse p r).mpr ((mem_source_packets p r).mp hr).1
  obtain ⟨w,he,hl⟩ := FiniteWindow.canonical_window_two_boundary_rank hn p G
    (joined_components_prices p hc).1 u v (hmov u hu) (hmov v hv)
    (joined_packet_cover_at_source p hc hk u hu) (joined_packet_cover_at_source p hc hk v hv)
    W rfl (by dsimp [W,sourceGapWindow]; omega) filling hGmatch x y hxy hy start finish hpositions
  have hm := (joined_components_prices p hc).2.1
  have hload := joined_port_load_mono p hc u
  refine ⟨filling,w,hmatch,he,?_⟩
  change (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
    2*(bridgeBudget (componentBridges p hc) : ℤ)-portLoad (displacement p.symm) u+_
  dsimp [G] at hl
  omega

#print axioms joined_source_gap_word
end LRX.FiniteCuts
