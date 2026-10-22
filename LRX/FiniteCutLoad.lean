import LRX.FiniteCutMass
import LRX.PortLoadMass

/-! Finite cut counts agree with the integer edge-crossing load used by actual
LRX services. The canonical finite lift has no hidden winding. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

def displacement (p : State b) (i : Fin b) : ℤ := (p i : ℤ)-(i : ℤ)

theorem canonical_lift (p : State b) : AffineLift.IsLift p.symm 0 (displacement p) := by
  unfold displacement
  simpa only [Equiv.symm_symm] using AffineLift.canonical_lift p.symm

def cutLoad (p : State b) (e : ℕ) : ℤ :=
  ∑ i : Fin b, PeriodicBuffer.edgePassages (b : ℤ)
    ((i : ℤ)-((e : ℤ)-1)) ((p i : ℤ)-((e : ℤ)-1))

theorem floor_at_cut (e : ℕ) (he : e ≤ b) (i : Fin b) :
    ((e : ℤ)-1-(i : ℤ))/(b : ℤ)=if i.val < e then 0 else -1 := by
  have hi := i.isLt
  have hb : (0 : ℤ) < b := by exact_mod_cast (show 0 < b by omega)
  split_ifs with h
  · apply PeriodicBuffer.quotient_eq_of_bounds hb <;> omega
  · apply PeriodicBuffer.quotient_eq_of_bounds hb <;> omega

theorem cut_arrow_load (p : State b) (e : ℕ) (he : e ≤ b) (i : Fin b) :
    PeriodicBuffer.edgePassages (b : ℤ) ((i : ℤ)-((e : ℤ)-1)) ((p i : ℤ)-((e : ℤ)-1))=
      (if i.val < e ∧ e ≤ (p i).val then (1 : ℤ) else 0)+
      (if (p i).val < e ∧ e ≤ i.val then 1 else 0) := by
  unfold PeriodicBuffer.edgePassages
  rw [show -((p i : ℤ)-((e : ℤ)-1))=(e : ℤ)-1-(p i : ℤ) by ring,
    show -((i : ℤ)-((e : ℤ)-1))=(e : ℤ)-1-(i : ℤ) by ring,
    floor_at_cut e he, floor_at_cut e he]
  by_cases h1 : i.val < e <;> by_cases h2 : (p i).val < e <;>
    simp [h1, h2, show (e ≤ i.val) ↔ ¬ i.val < e by omega,
      show (e ≤ (p i).val) ↔ ¬ (p i).val < e by omega]

theorem cut_load_eq_twice_half (p : State b) (e : ℕ) (he : e ≤ b) :
    cutLoad p e=2*(halfLoad p e : ℤ) := by
  unfold cutLoad
  simp_rw [cut_arrow_load p e he]
  rw [Finset.sum_add_distrib]
  have hf : (halfLoad p e : ℤ)=∑ i : Fin b, if i.val < e ∧ e ≤ (p i).val then (1 : ℤ) else 0 := by
    exact_mod_cast forward_as_sum p e
  have hb : ((backward p e).card : ℤ)=∑ i : Fin b, if (p i).val < e ∧ e ≤ i.val then (1 : ℤ) else 0 := by
    exact_mod_cast backward_as_sum p e
  rw [← hf, ← hb, ← cut_balance]
  change (halfLoad p e : ℤ)+(halfLoad p e : ℤ)= _
  ring

theorem port_load_eq_twice_half [NeZero b] (p : State b) (r : Fin b) :
    RotationWords.portLoad (displacement p) r=2*(halfLoad p (r.val+1) : ℤ) := by
  rw [RotationWords.port_load_original, ← cut_load_eq_twice_half p (r.val+1) (by have := r.isLt; omega)]
  apply Finset.sum_congr rfl
  intro i _
  unfold displacement
  congr 1 <;> push_cast <;> ring

#print axioms canonical_lift
#print axioms cut_load_eq_twice_half
#print axioms port_load_eq_twice_half
end LRX.FiniteCuts
