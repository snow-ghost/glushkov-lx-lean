import LRX.ReflectionTwoBlockNormalization
import LRX.FiniteZeroPortBarrier

namespace LRX.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The boundary between the two reversed blocks carries no load. -/
theorem two_block_reflection_zero_port (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) :
    portLoad (displacement p.symm) (⟨n/2-1,by omega⟩ : Fin n)=0 := by
  classical
  have hf : forward p.symm (n/2)=∅ := by
    ext i
    simp only [mem_forward,Finset.notMem_empty,iff_false,not_and]
    intro hi
    have hpi := (two_block_reflection_preserves_side hn p hp i).mpr hi
    omega
  have hl : halfLoad p.symm (n/2)=0 := by simp [halfLoad,hf]
  rw [port_load_eq_twice_half]
  have he : (⟨n/2-1,by omega⟩ : Fin n).val+1=n/2 := by simp only; omega
  rw [he,hl]
  simp

/-- Every load path stays inside one of the two reflected blocks. -/
theorem two_block_reflection_path_side (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i)
    {a b : Fin n} (hpath : CycleFootprint.LoadPath (displacement p.symm) a b) :
    a.val<n/2 ↔ b.val<n/2 := by
  have h := zero_port_path_side p (⟨n/2-1,by omega⟩ : Fin n)
    (two_block_reflection_zero_port hn p hp) hpath
  change (a.val ≤ n/2-1 ↔ b.val ≤ n/2-1) at h
  omega

/-- In normalized coordinates the full interval of a component fits in ceil(n/2) positions. -/
theorem two_block_reflection_component_span (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) (a : Fin n) :
    (componentRight p a).val-(componentLeft p a).val+1 ≤ n-n/2 := by
  have hl := two_block_reflection_path_side hn p hp (component_left_path p a)
  have hr := two_block_reflection_path_side hn p hp (component_right_path p a)
  have hright := (componentRight p a).isLt
  by_cases ha : a.val<n/2
  · have hL := hl.mp ha
    have hR := hr.mp ha
    omega
  · have hL : ¬(componentLeft p a).val<n/2 := fun h => ha (hl.mpr h)
    have hR : ¬(componentRight p a).val<n/2 := fun h => ha (hr.mpr h)
    omega

/-- The intrinsic component size is bounded, so the result survives changes of cut. -/
theorem two_block_reflection_component_card (hn : 2 ≤ n) (p : State n)
    (hp : ∀ i : Fin n, p.symm i=((n/2-1 : ℕ) : Fin n)-i) (a : Fin n) :
    (CycleFootprint.component (displacement p.symm) a).card ≤ n-n/2 := by
  classical
  by_cases ha : a.val<n/2
  · have hs : CycleFootprint.component (displacement p.symm) a ⊆
        Finset.univ.filter (fun i : Fin n => i.val<n/2) := by
      intro i hi
      have hpath := (CycleFootprint.mem_component _ _ _).mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(two_block_reflection_path_side hn p hp hpath).mp ha⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_filter_val_lt] at hc
    omega
  · let cut : Fin n := ⟨n/2,by omega⟩
    have hs : CycleFootprint.component (displacement p.symm) a ⊆ Finset.Ici cut := by
      intro i hi
      have hpath := (CycleFootprint.mem_component _ _ _).mp hi
      have hside := two_block_reflection_path_side hn p hp hpath
      apply Finset.mem_Ici.mpr
      change n/2 ≤ i.val
      omega
    have hc := Finset.card_le_card hs
    rw [Fin.card_Ici] at hc
    exact hc

#print axioms two_block_reflection_zero_port
#print axioms two_block_reflection_component_span
#print axioms two_block_reflection_component_card
end LRX.FiniteCuts
