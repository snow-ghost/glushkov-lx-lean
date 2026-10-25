import LRX.PaidRootService
import Mathlib

/-! The discount after recentering is exactly the load of the chosen original
physical edge, expressed by integer crossing counts at that cut. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem edge_passages_period {N : ℤ} (hN : N ≠ 0) (a b k : ℤ) :
    PeriodicBuffer.edgePassages N (a+k*N) (b+k*N)=PeriodicBuffer.edgePassages N a b := by
  have ha : -(a+k*N)=-a+(-k)*N := by ring
  have hb : -(b+k*N)=-b+(-k)*N := by ring
  simp only [PeriodicBuffer.edgePassages, ha, hb, Int.add_mul_ediv_right _ _ hN]
  congr 1
  ring

omit [NeZero n] in
theorem edge_passages_modEq {N : ℤ} (hN : N ≠ 0) {a b : ℤ}
    (h : Int.ModEq N a b) (d : ℤ) :
    PeriodicBuffer.edgePassages N a (a+d)=PeriodicBuffer.edgePassages N b (b+d) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  have hb : b=a+k*N := by nlinarith
  rw [hb, show a+k*N+d=(a+d)+k*N by ring, edge_passages_period hN]

theorem port_load_original (d : Fin n → ℤ) (r : Fin n) :
    portLoad d r=∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ)
      ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm (i : Fin n) : Int.ModEq (n : ℤ) (i : ℤ)
      (((L n^r.val) i : ℤ)-(r : ℤ)) := by
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self,
      AffineLift.rotation_power_apply, add_sub_cancel_right]
  calc
    portLoad d r = ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ)
        (((L n^r.val) i : ℤ)-(r : ℤ))
        (((L n^r.val) i : ℤ)-(r : ℤ)+d ((L n^r.val) i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact edge_passages_modEq hn (hm i) (d ((L n^r.val) i))
    _ = _ := Equiv.sum_comp (L n^r.val) (fun i => PeriodicBuffer.edgePassages (n : ℤ)
      ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i))

#print axioms port_load_original
end LRX.RotationWords
