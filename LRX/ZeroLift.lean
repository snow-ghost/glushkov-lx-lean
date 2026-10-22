import LRX.AffineCrossings

/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LRX word of length at most n-1. -/
namespace LRX.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]

theorem zero_lift_rotation {p : State n} {c : ℤ}
    (hd : IsLift p c (fun _ => 0)) : p = L n ^ (c : Fin n).val := by
  apply Equiv.ext
  intro i
  have h := lift_residue hd (p i)
  simp only [Int.cast_zero, add_zero, Equiv.symm_apply_apply] at h
  rw [rotation_power_apply, Fin.cast_val_eq_self]
  exact h

theorem zero_lift_word {p : State n} {c : ℤ}
    (hd : IsLift p c (fun _ => 0)) :
    ∃ w : List Letter, eval w = p ∧ w.length ≤ n - 1 := by
  refine ⟨List.replicate (c : Fin n).val .l, ?_, ?_⟩
  · rw [zero_lift_rotation hd]
    simp [eval, Letter.eval]
  · simp only [List.length_replicate]
    have h := (c : Fin n).isLt
    omega

theorem zero_lift_sharp_word (hn : 4 ≤ n) {p : State n} {c : ℤ}
    (hd : IsLift p c (fun _ => 0)) :
    ∃ w : List Letter, eval w = p ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w, he, hl⟩ := zero_lift_word hd
  refine ⟨w, he, hl.trans ?_⟩
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have h := Nat.mul_le_mul_right (n-1) (show 2 ≤ n by omega)
  simpa [mul_comm] using h

#print axioms zero_lift_sharp_word
end LRX.AffineLift
