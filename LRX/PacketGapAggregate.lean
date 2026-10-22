import LRX.PacketPartitionWidths

/-! Actual packet gaps supply the mass identity and all local energy bounds
used by the connected-branch square envelope. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

noncomputable def gapSquares (p : State n) (d : Fin n → ℤ) : ℤ :=
  ∑ a ∈ internalStarts p d, (size (PrunedLift.core p d 0) a : ℤ)^2

noncomputable def epsilon (d : Fin n → ℤ) : ℤ := (n : ℤ)^2/4-∑ i : Fin n, |d i|

noncomputable def complementReserve (p : State n) (d : Fin n → ℤ) : ℤ :=
  (n : ℤ)^2/4-(PrunedLift.coreHalfSize p d : ℤ)*(n-PrunedLift.coreHalfSize p d)

noncomputable def squareEnvelope (p : State n) (d : Fin n → ℤ) : ℤ :=
  gapSquares p d-2*complementReserve p d-2*PrunedLift.coreReserve p d

theorem gap_quadratic_cost {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) :
    ∃ K : ℕ, 2*gapEnergy p d a+(K : ℤ)^2 ≤ (size (PrunedLift.core p d 0) a : ℤ)^2 := by
  obtain ⟨filling,_,hdisp⟩ := packet_gap_filling hd hcover hroot a ha
  exact ⟨FiniteCuts.gapCost filling,by simpa only [gapEnergy,hdisp] using FiniteCuts.gapCost_quadratic filling⟩

theorem selected_gap_mass_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ internalStarts p d) (K : ℕ)
    (hK : 2*gapEnergy p d a+(K : ℤ)^2 ≤ (size (PrunedLift.core p d 0) a : ℤ)^2) :
    2*(∑ j ∈ internalStarts p d, gapEnergy p d j)+(K : ℤ)^2 ≤ gapSquares p d := by
  classical
  have hrest : (∑ j ∈ (internalStarts p d).erase a, 2*gapEnergy p d j) ≤
      ∑ j ∈ (internalStarts p d).erase a, (size (PrunedLift.core p d 0) j : ℤ)^2 := by
    apply Finset.sum_le_sum
    intro j hj
    exact gap_energy_square_cap hd hcover hroot j
      ((Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).1)
  rw [← Finset.mul_sum] at hrest
  have he := Finset.sum_erase_add (internalStarts p d) (gapEnergy p d) ha
  have hs := Finset.sum_erase_add (internalStarts p d)
    (fun j => (size (PrunedLift.core p d 0) j : ℤ)^2) ha
  unfold gapSquares
  omega

theorem localized_gap_energy {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ internalStarts p d) (K : ℕ)
    (hK : 2*gapEnergy p d a+(K : ℤ)^2 ≤ (size (PrunedLift.core p d 0) a : ℤ)^2) :
    (K : ℤ)^2 ≤ squareEnvelope p d+2*epsilon d := by
  have h := selected_gap_mass_bound hd hcover hroot a ha K hK
  have hmass := internal_gap_mass hd hcover hroot
  unfold squareEnvelope complementReserve epsilon PrunedLift.coreReserve
  nlinarith

theorem epsilon_nonneg {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) : 0 ≤ epsilon d := by
  have h := AffineLift.displacement_floor_cap hd.1 hm
  unfold epsilon AffineLift.displacement at *
  omega

theorem complement_reserve_nonneg (p : State n) (d : Fin n → ℤ) : 0 ≤ complementReserve p d := by
  have h : 4*((PrunedLift.coreHalfSize p d : ℤ)*(n-PrunedLift.coreHalfSize p d)) ≤ (n : ℤ)^2 := by
    nlinarith [sq_nonneg ((n : ℤ)-2*PrunedLift.coreHalfSize p d)]
  unfold complementReserve
  omega

#print axioms localized_gap_energy
#print axioms epsilon_nonneg
end LRX.FiniteGaps
