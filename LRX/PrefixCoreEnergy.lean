import LRX.AreaCorePartition
import LRX.ComponentPeakCapacity

namespace LRX.FiniteWindow
open FiniteCuts
variable {n b : ℕ}

/-- A filling in a zero-offset window has no greater half-load than its ambient map. -/
theorem prefix_window_half_load_le (W : Window n b) (hzero : W.offset = 0)
    (p : State n) (f : State b) (hm : ∀ i, p (embed W i) = embed W (f i)) (e : ℕ) :
    halfLoad f e ≤ halfLoad p e := by
  classical
  unfold halfLoad
  rw [← Finset.card_image_of_injective (forward f e) (embed_injective W)]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hil,hih⟩ := (mem_forward f e i).mp hi
  apply (mem_forward p e _).mpr
  rw [hm]
  simpa only [embed,hzero,Nat.zero_add] using And.intro hil hih

theorem prefix_window_peak_le (W : Window n b) (hzero : W.offset = 0)
    (p : State n) (f : State b) (hm : ∀ i, p (embed W i) = embed W (f i)) :
    leftPeak f b ≤ leftPeak p n := by
  apply Finset.sup_le
  intro e he
  have hb := W.fits
  have heN : e ∈ Finset.range (n+1) := by
    have heB := Finset.mem_range.mp he
    apply Finset.mem_range.mpr
    omega
  exact (prefix_window_half_load_le W hzero p f hm e).trans (Finset.le_sup heN)
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem source_target_displacement (p : State n) (i : Fin n) :
    displacement (sourceTarget p).symm i =
      if i ∈ sourcePackets p then displacement p.symm i else 0 := by
  classical
  by_cases hi : i ∈ sourcePackets p <;>
    simp [sourceTarget,PrunedLift.permutation_symm_apply,displacement,hi]

/-- The actual initial source core has energy bounded by the global source peak. -/
theorem prefix_core_energy_bound (p : State n)
    (hwidth : 2*sourceHalfPeak p ≤ (componentSet p 0).card) :
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤
      2*(sourceHalfPeak p : ℤ)*(((componentSet p 0).card : ℤ)-sourceHalfPeak p) := by
  classical
  let L := (componentSet p 0).card
  let W : Window n L := ⟨0,by simpa only [Nat.zero_add,Fintype.card_fin] using
    (Finset.card_le_univ (componentSet p 0))⟩
  have hW (i : Fin n) : Contains W i ↔ i.val < L := by simp [Contains,W]
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W (sourceTarget p) (fun i hi => by
    have hip : i ∈ componentSet p 0 := (zero_component_prefix p i).mpr ((hW i).mp hi)
    have hp := (CycleFootprint.mem_component _ _ _).mp hip
    have hpi : p.symm i ∈ componentSet p 0 := (CycleFootprint.mem_component _ _ _).mpr
      (hp.trans (CycleFootprint.arrow_target_load_path hd i))
    by_cases hs : i ∈ sourcePackets p
    · simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hs] using
        (hW _).mpr ((zero_component_prefix p _).mp hpi)
    · simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_neg hs] using hi)
  have hpeak : leftPeak f L ≤ sourceHalfPeak p :=
    prefix_window_peak_le W rfl (sourceTarget p).symm f hf
  have henergy := finite_energy_peak_upper f (sourceHalfPeak p) hpeak hwidth
  have he : (∑ i ∈ windowPositions W, |displacement (sourceTarget p).symm i|) =
      ∑ i, |displacement f i| := by
    rw [sum_window_positions]
    simp_rw [matching_window_displacement W (sourceTarget p).symm f hf]
  have hcore : (∑ i ∈ windowPositions W, |displacement (sourceTarget p).symm i|) =
      ∑ i ∈ prefixSourceCore p, |displacement p.symm i| := by
    simp only [windowPositions,prefixSourceCore,Finset.sum_filter]
    have hsum : (∑ i : Fin n, if i ∈ sourcePackets p then
        (if i.val < L then |displacement p.symm i| else 0) else 0) =
        ∑ i ∈ sourcePackets p, if i.val < L then |displacement p.symm i| else 0 := by
      have hset : Finset.univ.filter (fun i : Fin n => i ∈ sourcePackets p) = sourcePackets p := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [← Finset.sum_filter,hset]
    change (∑ i : Fin n, if Contains W i then |displacement (sourceTarget p).symm i| else 0) =
      ∑ i ∈ sourcePackets p, if i.val < L then |displacement p.symm i| else 0
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [source_target_displacement]
    by_cases hs : i ∈ sourcePackets p <;> by_cases hi : i.val < L <;>
      simp [hW,hs,hi]
  rw [hcore] at he
  rw [he]
  exact henergy

#print axioms prefix_core_energy_bound
end LRX.FiniteCuts
