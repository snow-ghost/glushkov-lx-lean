import LX.AnchorPhasePrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Two consecutive anchors cannot both miss the chosen neighboring pair.
The two excluded residues are 0 and 1, while an anchor step adds 2. -/
theorem reflection_two_anchor_choice (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a i : Fin n) :
    ∃ b : Fin n,(b=a ∨ b=a+1) ∧ 2 ≤ (cyclicOffset p b i).val := by
  by_cases ha : 2 ≤ (cyclicOffset p a i).val
  · exact ⟨a,Or.inl rfl,ha⟩
  · refine ⟨a+1,Or.inr rfl,?_⟩
    have he : cyclicOffset p (a+1) i=cyclicOffset p a i+2 := by
      unfold cyclicOffset
      simp only [hp]
      ring
    have hv : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [he,Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]
    omega

theorem reflection_neighbor_descent (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a i : Fin n) (hi : 2 ≤ (cyclicOffset p a i).val) :
    displacement p a (i+1)+1 < displacement p a i := by
  have he : cyclicOffset p a (i+1)=cyclicOffset p a i-2 := by
    unfold cyclicOffset
    simp only [hp]
    ring
  have hv : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)]
  have hle : (2 : Fin n) ≤ cyclicOffset p a i := by change (2 : Fin n).val ≤ _; omega
  have heval : (cyclicOffset p a (i+1)).val=(cyclicOffset p a i).val-2 := by
    rw [he,Fin.coe_sub_iff_le.mpr hle,hv]
  rw [displacement_offset,displacement_offset]
  omega


#print axioms reflection_two_anchor_choice
#print axioms reflection_neighbor_descent
end LX.AnchoredPhases
