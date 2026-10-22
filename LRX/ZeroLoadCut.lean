import LRX.LoadedFootprint
import LRX.PrunedExactService

/-! A zero-load cut at the end of a finite indexing interval forces the
original lifted endpoints to be the canonical finite endpoints. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem zero_load_each_arrow (d : Fin n → ℤ) (r : Fin n)
    (hz : RotationWords.portLoad d r=0) (i : Fin n) :
    PeriodicBuffer.edgePassages (n : ℤ) ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i)=0 := by
  rw [RotationWords.port_load_original] at hz
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp hz i (Finset.mem_univ i)

theorem zero_last_cut_endpoints (d : Fin n → ℤ) (r : Fin n) (hr : r.val+1=n)
    (hz : RotationWords.portLoad d r=0) (i : Fin n) :
    0 ≤ (i : ℤ)+d i ∧ (i : ℤ)+d i < (n : ℤ) := by
  have hN : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hi := i.isLt
  have hq : (-((i : ℤ)-(r : ℤ)))/(n : ℤ)=0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have he := zero_load_each_arrow d r hz i
  simp only [PeriodicBuffer.edgePassages,hq,sub_zero,abs_eq_zero] at he
  have hlo := Int.ediv_mul_le (-((i : ℤ)-(r : ℤ)+d i)) (ne_of_gt hN)
  have hhi := (Int.ediv_lt_iff_lt_mul hN).mp (show (-((i : ℤ)-(r : ℤ)+d i))/(n : ℤ) < 1 by omega)
  rw [he] at hlo
  norm_num at hlo hhi
  omega

theorem zero_last_cut_canonical {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hr : r.val+1=n)
    (hz : RotationWords.portLoad d r=0) (i : Fin n) :
    d i=(p.symm i : ℤ)-(i : ℤ) := by
  obtain ⟨hlo,hhi⟩ := zero_last_cut_endpoints d r hr hz i
  have hmod := hd.2 i
  change ((i : ℤ)+d i) % (n : ℤ)=((p.symm i : ℤ)+0) % (n : ℤ) at hmod
  rw [add_zero,Int.emod_eq_of_lt hlo hhi,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (p.symm i).isLt)] at hmod
  omega

/-- Every invariant union of cycles is separately balanced after a zero cut. -/
theorem zero_last_cut_balance {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hr : r.val+1=n)
    (hz : RotationWords.portLoad d r=0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) : (∑ i ∈ S, d i)=0 := by
  calc
    (∑ i ∈ S, d i)=∑ i ∈ S, ((p.symm i : ℤ)-(i : ℤ)) :=
      Finset.sum_congr rfl (fun i _ => zero_last_cut_canonical hd r hr hz i)
    _ = 0 := PrunedLift.canonical_balance p S hS

#print axioms zero_last_cut_canonical
#print axioms zero_last_cut_balance
end LRX.CycleFootprint
