import LRX.TwoBlockReverseRoute
import LRX.CyclicCutTargets
import LRX.RecenteredCrossings

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem half_load_zero_iff_invariant_cut (p : State n) (e : ℕ) :
    halfLoad p e=0 ↔ ∀ i : Fin n, (p i).val < e ↔ i.val < e := by
  constructor
  · intro hz
    have hf : forward p e=∅ := Finset.card_eq_zero.mp hz
    have hb : backward p e=∅ := Finset.card_eq_zero.mp (by rw [← cut_balance]; exact hz)
    intro i
    constructor
    · intro hi
      by_contra h
      have hm := (mem_backward p e i).mpr ⟨hi,by omega⟩
      rw [hb] at hm
      exact Finset.notMem_empty i hm
    · intro hi
      by_contra h
      have hm := (mem_forward p e i).mpr ⟨hi,by omega⟩
      rw [hf] at hm
      exact Finset.notMem_empty i hm
  · intro hcut
    have hf : forward p e=∅ := by
      ext i
      simp only [mem_forward,Finset.notMem_empty,iff_false,not_and]
      intro hi
      have hp := (hcut i).mpr hi
      omega
    simp [halfLoad,hf]

theorem invariant_cut_inverse (p : State n) (e : ℕ)
    (hcut : ∀ i : Fin n, (p i).val < e ↔ i.val < e) :
    ∀ i : Fin n, (p.symm i).val < e ↔ i.val < e := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (hcut (p.symm i)).symm

theorem invariant_cut_port_zero (p : State n) (e : ℕ) (he0 : 0<e) (hen : e≤n)
    (hcut : ∀ i : Fin n, (p i).val < e ↔ i.val < e) :
    portLoad (displacement p.symm) (⟨e-1,by omega⟩ : Fin n)=0 := by
  have hh := (half_load_zero_iff_invariant_cut p.symm e).mpr (invariant_cut_inverse p e hcut)
  rw [port_load_eq_twice_half]
  have hv : (⟨e-1,by omega⟩ : Fin n).val+1=e := by simp only; omega
  rw [hv,hh]
  simp

theorem zero_port_invariant_cut (p : State n) (r : Fin n)
    (hz : portLoad (displacement p.symm) r=0) :
    ∀ i : Fin n, (p i).val < r.val+1 ↔ i.val < r.val+1 := by
  rw [port_load_eq_twice_half] at hz
  have hh : halfLoad p.symm (r.val+1)=0 := by omega
  have hc := (half_load_zero_iff_invariant_cut p.symm (r.val+1)).mp hh
  simpa only [Equiv.symm_symm] using invariant_cut_inverse p.symm (r.val+1) hc

/-- A canonical zero cut preserves the finite inversion count after recentering. -/
theorem inversion_number_zero_recenter (p : State n) (z : Fin n)
    (hz : portLoad (displacement p.symm) z=0) :
    inversionNumber (localTarget p 0 (z+1))=inversionNumber p := by
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hcan := phase_zero_cut_canonical 0 z hd hz
  have h := inversion_count_recentered (0 : Fin n) (z+1) hd
  rw [hcan] at h
  have hend (q : State n) : (fun i : Fin n => (i : ℤ)+displacement q.symm i)=(fun i => (q.symm i : ℤ)) := by
    funext i; unfold displacement; omega
  rw [hend,hend,canonical_inversion_count,canonical_inversion_count] at h
  have hi (q : State n) : inversionNumber q.symm=inversionNumber q := inversion_number_inverse q
  simpa only [hi] using h

#print axioms invariant_cut_port_zero
#print axioms inversion_number_zero_recenter
end LRX.FiniteCuts
