import LRX.ZeroLoadCut

/-! Arbitrary zero cuts supply a finite coordinate potential. Every invariant
union of cycles therefore has zero total displacement. -/
namespace LRX.CycleFootprint
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def cutCoordinate (r i : Fin n) : ℤ := (i : ℤ)+(n : ℤ)*(((r : ℤ)-(i : ℤ))/(n : ℤ))

theorem zero_cut_displacement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hz : RotationWords.portLoad d r=0) (i : Fin n) :
    d i=cutCoordinate r (p.symm i)-cutCoordinate r i := by
  have hN : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm := hd.2 i
  simp only [add_zero] at hm
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hm
  have he := zero_load_each_arrow d r hz i
  simp only [PeriodicBuffer.edgePassages,abs_eq_zero,sub_eq_zero] at he
  have hleft : -((i : ℤ)-(r : ℤ)+d i)=(r : ℤ)-(p.symm i : ℤ)+k*(n : ℤ) := by nlinarith
  rw [hleft,Int.add_mul_ediv_right _ _ hN] at he
  have hright : -((i : ℤ)-(r : ℤ))=(r : ℤ)-(i : ℤ) := by ring
  rw [hright] at he
  unfold cutCoordinate
  nlinarith [congrArg (fun z : ℤ => z*(n : ℤ)) he]

theorem zero_cut_balance {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hz : RotationWords.portLoad d r=0)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S ↔ i ∈ S) : (∑ i ∈ S, d i)=0 := by
  calc
    (∑ i ∈ S, d i)=∑ i ∈ S, (cutCoordinate r (p.symm i)-cutCoordinate r i) :=
      Finset.sum_congr rfl (fun i _ => zero_cut_displacement hd r hz i)
    _ = 0 := by rw [Finset.sum_sub_distrib,PrunedLift.sum_inverse p S hS,sub_self]

#print axioms zero_cut_displacement
#print axioms zero_cut_balance
end LRX.CycleFootprint
