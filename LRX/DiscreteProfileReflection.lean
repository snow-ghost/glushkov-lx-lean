import LRX.DiscreteLoadProfile

/-! Reflection preserves the area and peak of a discrete load profile. -/
namespace LRX.DiscreteLoad
open scoped BigOperators
variable {b : ℕ}

def reflect (P : Profile b) : Profile b where
  height j := P.height (b-j)
  at_zero := by simpa using P.at_end
  at_end := by simpa using P.at_zero
  step_up j hj := by
    have h := P.step_down (b-(j+1)) (by omega)
    have he : b-(j+1)+1=b-j := by omega
    rwa [he] at h
  step_down j hj := by
    have h := P.step_up (b-(j+1)) (by omega)
    have he : b-(j+1)+1=b-j := by omega
    rwa [he] at h

theorem reflect_area (P : Profile b) : area (reflect P)=area P := by
  unfold area reflect
  simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect P.height (b+1)

theorem reflect_peak (P : Profile b) : peak (reflect P)=peak P := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact height_le_peak P (b-j) (by omega)
  · obtain ⟨j,hj,he⟩ := peak_attained P
    have h := height_le_peak (reflect P) (b-j) (by omega)
    have hj' : b-(b-j)=j := by omega
    simpa only [reflect,hj',he] using h

#print axioms reflect_area
#print axioms reflect_peak
end LRX.DiscreteLoad
