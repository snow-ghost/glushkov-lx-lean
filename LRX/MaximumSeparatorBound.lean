import LRX.RecenteredSupportWidth

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

def MaximalZeroCut (p : State n) : Prop :=
  ∀ t : Fin n, portLoad (displacement p.symm) t=0 →
    externalWidth (localTarget p 0 (t+1)) ≤ externalWidth p

theorem nonzero_component_left_port_zero (p : State n) (a : Fin n)
    (hv : componentLeft p a ≠ 0) : portLoad (displacement p.symm) (componentLeft p a-1)=0 := by
  let v := componentLeft p a
  change portLoad (displacement p.symm) (v-1)=0
  have hnon := port_load_nonneg (displacement p.symm) (v-1)
  by_contra hz
  have hpos : 0 < portLoad (displacement p.symm) (v-1) := by omega
  have hp : CycleFootprint.LoadPath (displacement p.symm) v (v-1) :=
    Relation.ReflTransGen.single (Or.inr ⟨by ring,hpos⟩)
  have hb := component_left_bound p a (v-1) ((component_left_path p a).trans hp)
  change v.val ≤ (v-1 : Fin n).val at hb
  rw [Fin.val_sub_one_of_ne_zero hv] at hb
  have hh := Fin.val_ne_zero_iff.mpr hv
  change v.val ≠ 0 at hh
  omega

theorem maximal_cut_bridge_width (p : State n) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (i : Fin k) :
    (bridgeEndpoints p hc i).2.val-(bridgeEndpoints p hc i).1.val ≤ externalWidth p := by
  let u := (bridgeEndpoints p hc i).1
  let v := (bridgeEndpoints p hc i).2
  have hv := ordered_component_bridge_valid p hc i
  have huS : u ∈ p.support := (mem_support_inverse p u).mpr (by
    intro h; have hh := congrArg Fin.val h; have hh' : (p.symm u).val < u.val := hv.2.1; omega)
  have hvS : v ∈ p.support := (mem_support_inverse p v).mpr (by
    intro h; have hh := congrArg Fin.val h; have hh' : v.val < (p.symm v).val := hv.2.2.1; omega)
  have hv0 : v ≠ 0 := by
    intro h
    have hh : u.val < v.val := hv.1
    rw [h,Fin.val_zero] at hh
    omega
  have hz := nonzero_component_left_port_zero p (componentOrder p hc i.succ) hv0
  have hb := hmax (v-1) hz
  have he : v-1+1=v := by ring
  rw [he,recentered_separator_width p u v hv.1 huS hvS hv.2.2.2] at hb
  exact hb

#print axioms maximal_cut_bridge_width
end LRX.FiniteCuts
