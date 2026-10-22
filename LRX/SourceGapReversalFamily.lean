import LRX.JointInternalExternalBudget
import LRX.SourceGapFilling
import LRX.FiniteGapPartition

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- Every positive internal source gap ending in the prescribed prefix. -/
noncomputable def positiveSourceGapStarts (p : State n) (L : ℕ) : Finset (Fin n) := by
  classical
  exact (sourcePackets p).filter (fun u =>
    FiniteGaps.next (sourcePackets p) u < n ∧
    FiniteGaps.next (sourcePackets p) u ≤ L ∧
    0 < portLoad (displacement p.symm) u)

@[simp] theorem mem_positive_source_gap_starts (p : State n) (L : ℕ) (u : Fin n) :
    u ∈ positiveSourceGapStarts p L ↔ u ∈ sourcePackets p ∧
      FiniteGaps.next (sourcePackets p) u < n ∧
      FiniteGaps.next (sourcePackets p) u ≤ L ∧
      0 < portLoad (displacement p.symm) u := by
  classical
  simp [positiveSourceGapStarts]

theorem positive_source_gap_filling_exists (p : State n) (L : ℕ)
    (u : {u // u ∈ positiveSourceGapStarts p L}) :
    ∃ f : State (FiniteGaps.size (sourcePackets p) u.val),
      ∀ i, p.symm (embed (FiniteGaps.window (sourcePackets p) u.val) i) =
        embed (FiniteGaps.window (sourcePackets p) u.val) (f i) := by
  have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
  obtain ⟨v,hv,he⟩ := FiniteGaps.next_is_member (sourcePackets p) u.val hu.2.1
  apply exists_restriction_of_inverse_closed
  intro x hx
  have hb := (FiniteGaps.contains_window (sourcePackets p) u.val x).mp hx
  have hxnot := FiniteGaps.gap_avoids_marks (sourcePackets p) u.val x
    ((FiniteGaps.mem_positions _ _ _).mpr hb)
  have hh := source_gap_inverse_inside p u.val v x hu.1 hv hxnot hb.1 (by omega)
  apply (FiniteGaps.contains_window _ _ _).mpr
  exact ⟨hh.1,by omega⟩

noncomputable def positiveSourceFilling (p : State n) (L : ℕ)
    (u : {u // u ∈ positiveSourceGapStarts p L}) : FillingWindow n :=
  ⟨FiniteGaps.size (sourcePackets p) u.val, FiniteGaps.window (sourcePackets p) u.val,
    Classical.choose (positive_source_gap_filling_exists p L u)⟩

noncomputable def positiveSourceFamily (p : State n) (L : ℕ) : List (FillingWindow n) :=
  (positiveSourceGapStarts p L).attach.toList.map (positiveSourceFilling p L)

theorem positive_source_family_spec (p : State n) (L : ℕ) :
    (∀ A ∈ positiveSourceFamily p L, A.Matches p.symm) ∧
    (positiveSourceFamily p L).Pairwise FillingWindow.Apart ∧
    (∀ A ∈ positiveSourceFamily p L, A.window.offset + A.size ≤ L) ∧
    (∀ A ∈ positiveSourceFamily p L, ∃ r : Fin n,
      r.val+1 = A.window.offset ∧ 0 < portLoad (displacement p.symm) r) := by
  classical
  have hm (u : {u // u ∈ positiveSourceGapStarts p L}) :
      (positiveSourceFilling p L u).Matches p.symm :=
    Classical.choose_spec (positive_source_gap_filling_exists p L u)
  refine ⟨?_,?_,?_,?_⟩
  · intro A hA
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
    exact hm u
  · apply List.pairwise_map.mpr
    apply (Finset.nodup_toList _).imp_of_mem
    intro u v _ _ huv i hi hj
    have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
    have hv := (mem_positive_source_gap_starts p L v.val).mp v.property
    have hne : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hd := FiniteGaps.gaps_disjoint (sourcePackets p) hu.1 hv.1 hne
    apply Finset.disjoint_left.mp hd
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  · intro A hA
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
    have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
    have hn := FiniteGaps.lt_next (sourcePackets p) u.val
    change u.val.val+1+(FiniteGaps.next (sourcePackets p) u.val-u.val.val-1) ≤ L
    omega
  · intro A hA
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
    have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
    exact ⟨u.val,rfl,hu.2.2.2⟩

/-- Every consecutive positive source gap in the prefix is included. -/
theorem consecutive_positive_gap_selected (p : State n) (L : ℕ) (u v : Fin n)
    (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p) (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u) (hvL : v.val ≤ L) :
    FiniteGaps.next (sourcePackets p) u = v.val ∧ u ∈ positiveSourceGapStarts p L := by
  have hle := FiniteGaps.next_le_member (sourcePackets p) u v hv huv
  have he : FiniteGaps.next (sourcePackets p) u = v.val := by
    by_contra h
    have hlt : FiniteGaps.next (sourcePackets p) u < v.val := by omega
    obtain ⟨x,hx,hxe⟩ := FiniteGaps.next_is_member (sourcePackets p) u (by have := v.isLt; omega)
    have hux := FiniteGaps.lt_next (sourcePackets p) u
    exact hgap x (by omega) (by omega) hx
  refine ⟨he,(mem_positive_source_gap_starts p L u).mpr ⟨hu,?_,?_,hpos⟩⟩
  · rw [he]; exact v.isLt
  · rw [he]; exact hvL

#print axioms consecutive_positive_gap_selected
#print axioms positive_source_gap_filling_exists
#print axioms positive_source_family_spec
end LRX.FiniteCuts
