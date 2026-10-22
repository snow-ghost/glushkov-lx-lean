import LRX.PacketGapWindows
import LRX.PacketEnergyReserve

/-! The total displacement mass splits exactly into the packet and its finite
fillings. Gaps unvisited by packet arrows have zero displacement. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def Internal (p : State n) (d : Fin n → ℤ) (a : Fin n) : Prop :=
  ∃ s x : Fin n, s ∈ PrunedLift.core p d 0 ∧ x ∈ positions (PrunedLift.core p d 0) a ∧
    BufferProgram.Touches (n : ℤ) (s : ℤ) (d s) (x : ℤ)

noncomputable def internalStarts (p : State n) (d : Fin n → ℤ) : Finset (Fin n) := by
  classical
  exact (PrunedLift.core p d 0).filter (Internal p d)

noncomputable def gapEnergy (p : State n) (d : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin (size (PrunedLift.core p d 0) a), |d (FiniteWindow.embed (window (PrunedLift.core p d 0) a) j)|

theorem core_zero (p : State n) (d : Fin n → ℤ) : (0 : Fin n) ∈ PrunedLift.core p d 0 :=
  (PrunedLift.mem_core p d 0 0).mpr ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩

theorem total_gap_mass (p : State n) (d : Fin n → ℤ) :
    (∑ i : Fin n, |d i|)=PrunedLift.coreEnergy p d+∑ a ∈ PrunedLift.core p d 0, gapEnergy p d a :=
  total_sum (PrunedLift.core p d 0) (core_zero p d) (fun i => |d i|)

theorem nonzero_gap_internal {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) (i : Fin n)
    (hi : i ∈ positions (PrunedLift.core p d 0) a) (hdi : d i ≠ 0) : Internal p d a := by
  obtain ⟨s,x,hrs,hsr,he,hxi⟩ := hcover i hdi
  have hs : s ∈ PrunedLift.core p d 0 := (PrunedLift.mem_core p d 0 s).mpr ⟨hrs,hsr⟩
  have hinv := packet_gap_invariant hd hcover hroot a ha
  have hx := PrunedLift.same_cycle_mem p _ hinv hi hxi.symm
  rcases he with hc | ⟨_,ht⟩
  · have hsgap := PrunedLift.same_cycle_mem p _ hinv hx hc.symm
    exact False.elim (gap_avoids_marks _ a s hsgap hs)
  · exact ⟨s,x,hs,hx,ht⟩

theorem noninternal_gap_zero {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) (hnot : ¬Internal p d a) : gapEnergy p d a=0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : FiniteWindow.embed (window (PrunedLift.core p d 0) a) i ∈ positions (PrunedLift.core p d 0) a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,FiniteWindow.contains_embed _ _⟩
  have hd0 : d (FiniteWindow.embed (window (PrunedLift.core p d 0) a) i)=0 := by
    by_contra h
    exact hnot (nonzero_gap_internal hd hcover hroot a ha _ hi h)
  exact abs_eq_zero.mpr hd0

theorem internal_gap_mass {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) :
    (∑ i : Fin n, |d i|)=PrunedLift.coreEnergy p d+∑ a ∈ internalStarts p d, gapEnergy p d a := by
  classical
  have he : (∑ a ∈ internalStarts p d, gapEnergy p d a)=∑ a ∈ PrunedLift.core p d 0, gapEnergy p d a := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    have hn : ¬Internal p d a := fun h => hnot (Finset.mem_filter.mpr ⟨ha,h⟩)
    exact noninternal_gap_zero hd hcover hroot a ha hn
  rw [he]
  exact total_gap_mass p d

theorem gap_energy_nonneg (p : State n) (d : Fin n → ℤ) (a : Fin n) : 0 ≤ gapEnergy p d a :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem gap_energy_square_cap {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) :
    2*gapEnergy p d a ≤ (size (PrunedLift.core p d 0) a : ℤ)^2 := by
  obtain ⟨filling,_,hdisp⟩ := packet_gap_filling hd hcover hroot a ha
  simpa only [gapEnergy,hdisp] using FiniteCuts.finite_energy_square_cap filling

#print axioms internal_gap_mass
#print axioms gap_energy_square_cap
end LRX.FiniteGaps
