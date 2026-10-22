import LRX.InvariantCutInversionBudget
import LRX.LoadComponentCardRecenter
import Mathlib.Order.Interval.Finset.Fin

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Canonical load components have no holes in the linear order. -/
theorem component_set_eq_interval (p : State n) (a : Fin n) :
    componentSet p a = Finset.Icc (componentLeft p a) (componentRight p a) := by
  classical
  ext x
  constructor
  · intro hx
    have hp := (CycleFootprint.mem_component _ _ _).mp hx
    exact Finset.mem_Icc.mpr ⟨component_left_bound p a x hp, component_right_bound p a x hp⟩
  · intro hx
    obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hx
    change (componentLeft p a).val ≤ x.val at hl
    change x.val ≤ (componentRight p a).val at hr
    have hp := (CycleFootprint.load_path_symm _ (component_left_path p a)).trans
      (component_right_path p a)
    have hpath := CycleFootprint.integer_load_path (displacement p.symm)
      ((componentLeft p a : Fin n) : ℤ) (x : ℤ) (by exact_mod_cast hl) (by
        intro z hz hx
        have hz0 : 0 ≤ z := le_trans (by positivity) hz
        have hzn : z < n := lt_trans hx (by exact_mod_cast x.isLt)
        have hv : ((z : Fin n).val : ℤ) = z := by
          simp only [Fin.val_intCast]
          rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_eq_of_lt hz0 hzn]
        exact load_path_crossed_port_positive p hp (z : Fin n) (by omega) (by omega))
    have hx' : CycleFootprint.LoadPath (displacement p.symm) (componentLeft p a) x := by
      simpa only [Int.cast_natCast, Fin.cast_val_eq_self] using hpath
    exact (CycleFootprint.mem_component _ _ _).mpr ((component_left_path p a).trans hx')

theorem component_card_eq_width (p : State n) (a : Fin n) :
    (componentSet p a).card = (componentRight p a).val + 1 - (componentLeft p a).val := by
  rw [component_set_eq_interval, Fin.card_Icc]

/-- The port immediately after the component is unloaded, including the last port. -/
theorem component_right_port_zero (p : State n) (a : Fin n) :
    portLoad (displacement p.symm) (componentRight p a) = 0 := by
  have hnon := port_load_nonneg (displacement p.symm) (componentRight p a)
  by_contra hz
  have hpos : 0 < portLoad (displacement p.symm) (componentRight p a) := by omega
  have hend := finite_positive_port_before_end p (componentRight p a) hpos
  have hp : CycleFootprint.LoadPath (displacement p.symm)
      (componentRight p a) (componentRight p a + 1) :=
    Relation.ReflTransGen.single (Or.inl ⟨rfl,hpos⟩)
  have hb := component_right_bound p a _ ((component_right_path p a).trans hp)
  rw [Fin.val_add_one_of_lt' hend] at hb
  omega

/-- A canonical component starts immediately after a zero port. -/
theorem component_left_port_zero (p : State n) (a : Fin n) :
    portLoad (displacement p.symm) (componentLeft p a - 1) = 0 := by
  by_cases h : componentLeft p a = 0
  · have hz := invariant_cut_port_zero p n (Nat.pos_of_ne_zero (NeZero.ne n)) le_rfl
      (fun i => iff_of_true (p i).isLt i.isLt)
    have he : (componentLeft p a - 1 : Fin n) = ⟨n-1,by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩ := by
      rw [h]
      apply Fin.ext
      cases n with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ k => simp
    rw [he]
    exact hz
  · exact nonzero_component_left_port_zero p a h

#print axioms component_set_eq_interval
#print axioms component_card_eq_width
#print axioms component_right_port_zero
#print axioms component_left_port_zero
end LRX.FiniteCuts
