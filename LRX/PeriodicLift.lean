import LRX.AffineLift
import Mathlib

/-! Turn the finite balanced lift into a genuine periodic bijection of integers.
This supplies the object on which affine crossings and routing are defined. -/
namespace LRX.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

theorem residue_val (z : ℤ) : ((Fin.intCast z : Fin n) : ℤ) = z % (n : ℤ) := by
  change ((z : Fin n).val : ℤ) = _
  rw [Fin.val_intCast]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt modulus_pos))

omit [NeZero n] in
theorem fin_mod (i : Fin n) : (i : ℤ) % n = (i : ℤ) :=
  Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)

theorem residue_fin (i : Fin n) : (Fin.intCast (i : ℤ) : Fin n) = i := by
  apply Fin.ext
  have h := residue_val (n := n) (i : ℤ)
  rw [fin_mod] at h
  exact_mod_cast h

theorem residue_period (z k : ℤ) :
    (Fin.intCast (z + k * (n : ℤ)) : Fin n) = (Fin.intCast z : Fin n) := by
  apply Fin.ext
  have h : ((Fin.intCast (z + k * (n : ℤ)) : Fin n) : ℤ) = ((Fin.intCast z : Fin n) : ℤ) := by
    rw [residue_val, residue_val]
    simp
  exact_mod_cast h

theorem modEq_residue (z : ℤ) :
    Int.ModEq (n : ℤ) z ((Fin.intCast z : Fin n) : ℤ) := by
  rw [residue_val]
  simp [Int.ModEq]

def periodicMap (d : Fin n → ℤ) (z : ℤ) : ℤ := z + d (Fin.intCast z : Fin n)

theorem periodicMap_fin (d : Fin n → ℤ) (i : Fin n) :
    periodicMap d (i : ℤ) = (i : ℤ) + d i := by
  simp only [periodicMap, residue_fin]

theorem periodicMap_add (d : Fin n → ℤ) (z k : ℤ) :
    periodicMap d (z + k * (n : ℤ)) = periodicMap d z + k * n := by
  simp only [periodicMap, residue_period]
  ring

theorem periodicMap_endpoint {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (z : ℤ) :
    Int.ModEq (n : ℤ) (periodicMap d z) ((p.symm (Fin.intCast z : Fin n) : ℤ) + c) := by
  exact ((modEq_residue z).add (Int.ModEq.refl (d (Fin.intCast z : Fin n)))).trans (hd.2 _)

theorem periodicMap_injective {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : Function.Injective (periodicMap d) := by
  intro a b hab
  have ha := periodicMap_endpoint hd a
  have hb := periodicMap_endpoint hd b
  rw [hab] at ha
  have h := (ha.symm.trans hb).add_right_cancel' c
  simp only [Int.ModEq, fin_mod] at h
  have hindex : (Fin.intCast a : Fin n) = (Fin.intCast b : Fin n) := by
    apply p.symm.injective
    apply Fin.ext
    exact_mod_cast h
  simp only [periodicMap, hindex] at hab
  omega

theorem periodicMap_surjective {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : Function.Surjective (periodicMap d) := by
  intro y
  let j : Fin n := (Fin.intCast (y - c) : Fin n)
  let i : Fin n := p j
  have hbase : Int.ModEq (n : ℤ) ((i : ℤ) + d i) y := by
    have hi := hd.2 i
    have hj := (modEq_residue (n := n) (y - c)).symm.add_right c
    have he : p.symm i = j := p.symm_apply_apply j
    rw [he] at hi
    exact hi.trans (by simpa [j] using hj)
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hbase
  refine ⟨(i : ℤ) + k * n, ?_⟩
  rw [periodicMap_add, periodicMap_fin]
  linarith [hk]

/-- This is the actual affine permutation, not an assumed abstract routing profile. -/
noncomputable def periodicEquiv {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : ℤ ≃ ℤ :=
  Equiv.ofBijective (periodicMap d) ⟨periodicMap_injective hd, periodicMap_surjective hd⟩


theorem normalize_phase {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : IsLift p ((Fin.intCast c : Fin n) : ℤ) d := by
  refine ⟨hd.1, ?_⟩
  intro i
  exact (hd.2 i).trans ((modEq_residue c).add_left (p.symm i : ℤ))


#print axioms periodicMap_injective
#print axioms periodicMap_surjective
end LRX.AffineLift
