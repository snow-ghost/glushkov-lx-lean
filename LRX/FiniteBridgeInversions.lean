import LRX.FiniteBridgeCoordinates

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem component_bridge_inversions (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → p x=x) :
    inversionNumber (componentBridge p u v)=inversionNumber p+(2*(v.val-u.val)-1) := by
  let g : Fin n := ⟨v.val-u.val,by have := v.isLt; omega⟩
  have hg : g.val+u.val=v.val := by dsimp [g]; omega
  have hgpos : 0 < g.val := by dsimp [g]; omega
  have hg0 : g ≠ 0 := by intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega
  have hgu : g+u=v := by
    apply Fin.ext
    rw [Fin.val_add,hg,Nat.mod_eq_of_lt v.isLt]
  obtain ⟨h0,hv⟩ := bridge_centered_endpoints p u v g hgu hg
  have hfixed : ∀ i : Fin n, 0 < i.val → i.val < g.val →
      centeredInverse (componentBridge p u v) u i=(i : ℤ) := by
    intro i hi hig
    have hsum : (i+u).val=i.val+u.val := by
      rw [Fin.val_add,Nat.mod_eq_of_lt (by have := v.isLt; omega)]
    have hlo : u.val < (i+u).val := by omega
    have hhi : (i+u).val < v.val := by omega
    have hx := hgap (i+u) hlo hhi
    have hxi : p.symm (i+u)=i+u := by
      simpa only [Equiv.symm_apply_apply] using (congrArg p.symm hx).symm
    have hnu : i+u ≠ u := by intro he; have := congrArg Fin.val he; omega
    have hnv : i+u ≠ v := by intro he; have := congrArg Fin.val he; omega
    rw [centered_inverse_eq,component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hnu hnv,hxi]
    ring
  have he := ZeroGap.endpoint_swap_inversions (centeredInverse (componentBridge p u v) u) g hgpos
    (by rw [h0]; omega) (by rw [hv]; omega) (by
      rw [h0,hv]
      have hu' := (p.symm u).isLt
      have hv' := (p.symm v).isLt
      omega) hfixed
  rw [bridge_centered_swap p u v g hgu hg hg0,centered_inverse_count,centered_inverse_count] at he
  exact he

#print axioms component_bridge_inversions
end LRX.FiniteCuts
