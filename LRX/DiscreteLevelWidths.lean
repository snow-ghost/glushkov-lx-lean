import LRX.DiscreteLoadProfile

/-! Superlevel widths are bounded by the endpoint slopes. Above a prefix
cap, their left endpoint is shifted by the distance from that prefix. -/
namespace LRX.DiscreteLoad
open scoped BigOperators
variable {b : ℕ}

theorem peak_after_prefix (P : Profile b) (y u : ℕ) (hy : y ≤ b)
    (hprefix : ∀ j, j ≤ y → P.height j ≤ u) (hu : u < peak P) :
    y+2*peak P ≤ b+u := by
  obtain ⟨j,hj,he⟩ := peak_attained P
  have hyj : y < j := by by_contra h; have := hprefix j (by omega); omega
  have hstep := (height_step P y j (by omega) hj).1
  have hcap := (height_capacity P j hj).2
  have hpy := hprefix y le_rfl
  omega

theorem level_width (P : Profile b) (h : ℕ) (hh : h < peak P) :
    ((level P h).card : ℤ) ≤ (b : ℤ)-2*h-1 := by
  have hs : level P h ⊆ Finset.Icc (h+1) (b-h-1) := by
    intro j hj
    obtain ⟨hj,hheight⟩ := Finset.mem_filter.mp hj
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    obtain ⟨hlo,hhi⟩ := height_capacity P j hjb
    apply Finset.mem_Icc.mpr
    omega
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  have hp := twice_peak_le P
  omega

theorem level_width_after_prefix (P : Profile b) (y u h : ℕ) (hy : y ≤ b)
    (hprefix : ∀ j, j ≤ y → P.height j ≤ u) (hu : u ≤ h) (hh : h < peak P) :
    ((level P h).card : ℤ) ≤ (b : ℤ)-y+u-2*h-1 := by
  have hs : level P h ⊆ Finset.Icc (y+(h+1-u)) (b-h-1) := by
    intro j hj
    obtain ⟨hj,hheight⟩ := Finset.mem_filter.mp hj
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    have hyj : y < j := by by_contra hn; have := hprefix j (by omega); omega
    have hstep := (height_step P y j (by omega) hjb).1
    have hpy := hprefix y le_rfl
    have hcap := (height_capacity P j hjb).2
    apply Finset.mem_Icc.mpr
    omega
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  have hp := peak_after_prefix P y u hy hprefix (by omega)
  omega

#print axioms level_width
#print axioms level_width_after_prefix
end LRX.DiscreteLoad
