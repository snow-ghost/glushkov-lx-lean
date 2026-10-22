import LRX.ComponentFillingWindow
import LRX.SuffixComponentParameters

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem suffix_component_window_exists (p : State n) (L : ℕ)
    (C : {C // C ∈ nontrivialSuffixComponents p L}) :
    ∃ A : FillingWindow n, A.size = C.val.card ∧
      (∀ i, Contains A.window i ↔ i ∈ C.val) ∧ A.Matches p.symm := by
  classical
  have hC := (Finset.mem_filter.mp C.property).1
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hC
  obtain ⟨A,hsize,hpos,hm⟩ := exists_component_filling_window p a
  change componentSet p a = C.val at ha
  rw [ha] at hsize hpos
  exact ⟨A,hsize,hpos,hm⟩

noncomputable def suffixComponentFilling (p : State n) (L : ℕ)
    (C : {C // C ∈ nontrivialSuffixComponents p L}) : FillingWindow n :=
  Classical.choose (suffix_component_window_exists p L C)

noncomputable def suffixComponentFamily (p : State n) (L : ℕ) : List (FillingWindow n) :=
  (nontrivialSuffixComponents p L).attach.toList.map (suffixComponentFilling p L)

theorem suffix_component_filling_spec (p : State n) (L : ℕ)
    (C : {C // C ∈ nontrivialSuffixComponents p L}) :
    (suffixComponentFilling p L C).size = C.val.card ∧
      (∀ i, Contains (suffixComponentFilling p L C).window i ↔ i ∈ C.val) ∧
      (suffixComponentFilling p L C).Matches p.symm :=
  Classical.choose_spec (suffix_component_window_exists p L C)

theorem suffix_component_family_spec (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    (∀ A ∈ suffixComponentFamily p L, A.Matches p.symm) ∧
    (suffixComponentFamily p L).Pairwise FillingWindow.Apart ∧
    (∀ A ∈ suffixComponentFamily p L, L ≤ A.window.offset) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨C,_,rfl⟩ := List.mem_map.mp hA
    exact (suffix_component_filling_spec p L C).2.2
  · apply List.pairwise_map.mpr
    apply (Finset.nodup_toList _).imp_of_mem
    intro C D _ _ hne i hi hj
    have hd := CycleFootprint.component_blocks_disjoint (displacement p.symm)
      (suffixVertices n L) (Finset.mem_filter.mp C.property).1
      (Finset.mem_filter.mp D.property).1 (fun h => hne (Subtype.ext h))
    exact Finset.disjoint_left.mp hd
      ((suffix_component_filling_spec p L C).2.1 i |>.mp hi)
      ((suffix_component_filling_spec p L D).2.1 i |>.mp hj)
  · intro A hA
    obtain ⟨C,_,rfl⟩ := List.mem_map.mp hA
    obtain ⟨hs,hpos,_⟩ := suffix_component_filling_spec p L C
    have hc := (Finset.mem_filter.mp C.property).2
    let i : Fin (suffixComponentFilling p L C).size := ⟨0,by omega⟩
    have hi := (hpos _).mp (contains_embed (suffixComponentFilling p L C).window i)
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp C.property).1
    rw [← he] at hi
    have hb := invariant_suffix_closed p L hLn hcut a ha _
      ((CycleFootprint.mem_component _ _ _).mp hi)
    rw [mem_suffix_vertices] at hb
    simpa only [embed,i,Nat.add_zero] using hb

#print axioms suffix_component_family_spec
end LRX.FiniteCuts
