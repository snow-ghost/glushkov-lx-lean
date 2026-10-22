import LRX.OriginalPeakCutoff
import LRX.ConnectedEventDefect

namespace LRX.FiniteCuts
open RotationWords ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The canonical left root of a proper load component reaches every moving
vertex of that component, including when the left endpoint is zero. -/
theorem component_root_reaches (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (a : Fin n) (ha : a ∈ componentRoots p)
    (i : Fin n) (hi : p.symm i ≠ i)
    (hpath : CycleFootprint.LoadPath (displacement p.symm) a i) : FiniteReach p a i := by
  have hsize := component_root_card_ge_two p a ha
  have hlroot := nontrivial_component_left_root p a hsize
  have he : componentLeft p a=a := component_roots_unique p hlroot ha
    (CycleFootprint.load_path_symm _ (component_left_path p a))
  have hproper := component_card_lt_of_multiple_roots p hm a
  have hw := component_card_eq_width p a
  have hmove := component_root_moved p a ha
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) a (a-1) := by
    intro hp
    have hlo := component_left_bound p a (a-1) hp
    have hhi := component_right_bound p a (a-1) hp
    rw [he] at hlo
    by_cases hz : a=0
    · have hOne : (1 : Fin n).val=1 := by change 1%n=1; exact Nat.mod_eq_of_lt hn
      have hv : (a-1 : Fin n).val=n-1 := by
        rw [Fin.val_sub,hOne,hz,Fin.val_zero,Nat.add_zero,Nat.mod_eq_of_lt (by omega)]
      rw [hv] at hhi
      rw [he,hz,Fin.val_zero] at hw
      rw [hz] at hproper hhi
      omega
    · rw [Fin.val_sub_one_of_ne_zero hz] at hlo
      have := Fin.val_ne_zero_iff.mpr hz
      omega
  exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm)
    ⟨a,hmove⟩ (a-1) (Or.inr (by ring)) hout ⟨i,hi⟩ hpath

/-- True source packets and actual filling cycles cover the sorting-event
graph with one seed per load component and one per filling cycle. -/
theorem source_packet_event_cover (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (events : List (Event n))
    (hprod : (events.map eventSwap).prod=p) (hsep : events.Pairwise LaterOutside)
    (htravel : ∀ i, Travel events i (p.symm i) (displacement p.symm i)) :
    p.support.card ≤ events.length+(componentRoots p).card+(fillingCycles p).card := by
  classical
  let roots := p.supportᶜ.toList ++ (componentRoots p).toList ++
    (fillingCycles p).toList.map cycleRoot
  have hcover (i : Fin n) : ∃ r ∈ roots, EventReaches events r i := by
    by_cases hi : i ∈ p.support
    · by_cases hs : i ∈ sourcePackets p
      · obtain ⟨a,ha,hpath⟩ := component_roots_cover p i ((mem_support_inverse p i).mp hi)
        have hp := component_root_reaches hn p hm a ha i ((mem_support_inverse p i).mp hi) hpath
        have hc : PrunedLift.InCore p (displacement p.symm) a i :=
          ⟨hp,((mem_source_packets p i).mp hs).2 a hp⟩
        refine ⟨a,?_,core_event_reachable hprod hsep htravel hc⟩
        simp only [roots,List.mem_append,List.mem_map,Finset.mem_toList]
        exact Or.inl (Or.inr ha)
      · have hinv : i ∈ (p⁻¹).support := by simpa only [Equiv.Perm.support_inv] using hi
        obtain ⟨q,hq,hiq⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hinv
        have hqfill : q ∈ fillingCycles p := by
          apply Finset.mem_filter.mpr
          refine ⟨hq,Finset.disjoint_left.mpr ?_⟩
          intro j hj hjs
          have hc := (cycle_root_same_cycle hq hiq).symm.trans (cycle_root_same_cycle hq hj)
          exact hs (source_packets_predecessor_closed p i j (Or.inl hc) hjs)
        refine ⟨cycleRoot q,?_,cycle_event_reachable events p hprod (cycle_root_same_cycle hq hiq)⟩
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨q,Finset.mem_toList.mpr hqfill,rfl⟩
    · refine ⟨i,?_,Relation.ReflTransGen.refl⟩
      apply List.mem_append_left
      apply List.mem_append_left
      exact Finset.mem_toList.mpr (Finset.mem_compl.mpr hi)
  have h := root_cover_count events roots hcover
  simp only [roots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin] at h
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  omega

#print axioms component_root_reaches
#print axioms source_packet_event_cover
end LRX.FiniteCuts
