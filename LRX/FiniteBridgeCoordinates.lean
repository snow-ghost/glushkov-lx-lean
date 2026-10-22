import LRX.FiniteComponentBridge
import LRX.ZeroGapInversionSum
import LRX.RecenteredCrossings

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def centeredInverse (p : State n) (u i : Fin n) : ℤ :=
  (i : ℤ)+RotationWords.localDisplacement (displacement p.symm) u i

theorem centered_inverse_eq (p : State n) (u i : Fin n) :
    centeredInverse p u i=(i : ℤ)+(p.symm (i+u) : ℤ)-((i+u).val : ℤ) := by
  simp only [centeredInverse,RotationWords.localDisplacement,AffineLift.rotation_power_apply,
    Fin.cast_val_eq_self,displacement]
  ring

theorem centered_inverse_count (p : State n) (u : Fin n) :
    LiftedModel.inversionCount (centeredInverse p u)=inversionNumber p := by
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Equiv.symm_symm,Fin.val_zero,Int.natCast_zero] using canonical_lift p.symm
  have he := RotationWords.inversion_count_recentered 0 u hd
  change LiftedModel.inversionCount (centeredInverse p u)=_ at he
  have hfun : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=(fun i => (p.symm i : ℤ)) := by
    funext i
    simp [displacement]
  rw [hfun,canonical_inversion_count] at he
  rw [show inversionNumber p.symm=inversionNumber p from inversion_number_inverse p] at he
  exact he

theorem bridge_centered_endpoints (p : State n) (u v g : Fin n)
    (hgu : g+u=v) (hg : g.val+u.val=v.val) :
    centeredInverse (componentBridge p u v) u 0=(p.symm v : ℤ)-(u : ℤ) ∧
    centeredInverse (componentBridge p u v) u g=(p.symm u : ℤ)-(u : ℤ) := by
  constructor
  · rw [centered_inverse_eq]
    simp only [zero_add,Fin.val_zero,Int.natCast_zero,component_bridge_inverse,Equiv.swap_apply_left]
  · rw [centered_inverse_eq,hgu,component_bridge_inverse,Equiv.swap_apply_right]
    omega

theorem bridge_centered_swap (p : State n) (u v g : Fin n)
    (hgu : g+u=v) (hg : g.val+u.val=v.val) (hg0 : g ≠ 0) :
    ZeroGap.swapEndpoints (centeredInverse (componentBridge p u v) u) g=centeredInverse p u := by
  obtain ⟨h0,hg'⟩ := bridge_centered_endpoints p u v g hgu hg
  funext i
  unfold ZeroGap.swapEndpoints
  by_cases hi : i=0
  · subst i
    rw [Equiv.swap_apply_left,hg',centered_inverse_eq]
    simp
  · by_cases hig : i=g
    · subst i
      rw [Equiv.swap_apply_right,h0,centered_inverse_eq,hgu]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hi hig]
      have hne0 : i+u ≠ u := by
        intro he
        have he' : i+u=0+u := by simpa using he
        exact hi (add_right_cancel he')
      have hneg : i+u ≠ v := by
        intro he
        have he' : i+u=g+u := he.trans hgu.symm
        exact hig (add_right_cancel he')
      rw [centered_inverse_eq,centered_inverse_eq,component_bridge_inverse,
        Equiv.swap_apply_of_ne_of_ne hne0 hneg]

#print axioms centered_inverse_count
#print axioms bridge_centered_swap
end LRX.FiniteCuts
