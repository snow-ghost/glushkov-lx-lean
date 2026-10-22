import LRX.JoinedBridgeGapWord

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem left_component_outer_source (hn : 2 ≤ n) (p : State n) (a : CycleFootprint.Active p)
    (hroom : (componentRight p a.val).val+1 < n) :
    componentLeft p a.val ∈ sourcePackets p ∧
      portLoad (displacement p.symm) (componentLeft p a.val-1)=0 := by
  let l := componentLeft p a.val
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hadj : CycleFootprint.Adjacent l (l-1) := Or.inr (by ring)
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) l (l-1) := by
    intro hp
    have hlo := component_left_bound p a.val (l-1) ((component_left_path p a.val).trans hp)
    have hhi := component_right_bound p a.val (l-1) ((component_left_path p a.val).trans hp)
    change l.val ≤ (l-1 : Fin n).val at hlo
    by_cases hz : l=0
    · have hOne : (1 : Fin n).val=1 := by change 1%n=1; exact Nat.mod_eq_of_lt (by omega)
      have he : (l-1 : Fin n).val=n-1 := by
        rw [Fin.val_sub,hOne,hz,Fin.val_zero,Nat.add_zero,Nat.mod_eq_of_lt (by omega)]
      rw [he] at hhi
      omega
    · rw [Fin.val_sub_one_of_ne_zero hz] at hlo
      have := Fin.val_ne_zero_iff.mpr hz
      omega
  have hm := CycleFootprint.load_boundary_active hd (displacement_short p.symm) a l (l-1)
    (component_left_path p a.val) hadj hout
  constructor
  · apply component_universal_source p l hm
    intro x hx hp
    exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm) ⟨l,hm⟩ (l-1) hadj hout ⟨x,hx⟩ hp
  · change portLoad (displacement p.symm) (l-1)=0
    have hnon := port_load_nonneg (displacement p.symm) (l-1)
    by_contra hz
    have hpos : 0 < portLoad (displacement p.symm) (l-1) := by omega
    exact hout (Relation.ReflTransGen.single (Or.inr ⟨by ring,hpos⟩))

theorem right_component_outer_source (hn : 2 ≤ n) (p : State n) (a : CycleFootprint.Active p)
    (hroom : 0 < (componentLeft p a.val).val) :
    componentRight p a.val ∈ sourcePackets p ∧
      portLoad (displacement p.symm) (componentRight p a.val)=0 := by
  let r := componentRight p a.val
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hadj : CycleFootprint.Adjacent r (r+1) := Or.inl rfl
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) r (r+1) := by
    intro hp
    have hlo := component_left_bound p a.val (r+1) ((component_right_path p a.val).trans hp)
    have hhi := component_right_bound p a.val (r+1) ((component_right_path p a.val).trans hp)
    change (r+1 : Fin n).val ≤ r.val at hhi
    by_cases he : r.val+1 < n
    · rw [Fin.val_add_one_of_lt' he] at hhi
      omega
    · have hh : r.val+1=n := by have := r.isLt; omega
      have hOne : (1 : Fin n).val=1 := by change 1%n=1; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add,hOne,hh,Nat.mod_self] at hlo
      omega
  have hm := CycleFootprint.load_boundary_active hd (displacement_short p.symm) a r (r+1)
    (component_right_path p a.val) hadj hout
  constructor
  · apply component_universal_source p r hm
    intro x hx hp
    exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm) ⟨r,hm⟩ (r+1) hadj hout ⟨x,hx⟩ hp
  · change portLoad (displacement p.symm) r=0
    have hnon := port_load_nonneg (displacement p.symm) r
    by_contra hz
    have hpos : 0 < portLoad (displacement p.symm) r := by omega
    exact hout (Relation.ReflTransGen.single (Or.inl ⟨rfl,hpos⟩))

#print axioms left_component_outer_source
#print axioms right_component_outer_source
end LRX.FiniteCuts
