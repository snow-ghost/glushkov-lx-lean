import LRX.PrunedService

/-! A finite cycle path crosses every position between two of its vertices.
This supplies the geometric root star for a finite enclosing root cycle. -/
namespace LRX.PrunedLift
variable {n : ℕ}

theorem cycle_path_crosses (p : State n) (u j : Fin n) (k : ℕ)
    (hu : u.val ≤ j.val) (hv : j.val ≤ (((p⁻¹)^k) u).val) :
    ∃ a : Fin n, (p⁻¹).SameCycle u a ∧
      min a.val ((p⁻¹) a).val ≤ j.val ∧ j.val ≤ max a.val ((p⁻¹) a).val := by
  induction k with
  | zero =>
    have hj : j.val=u.val := by simpa using Nat.le_antisymm hv hu
    exact ⟨u, Equiv.Perm.SameCycle.refl _ _, by omega, by omega⟩
  | succ k ih =>
    by_cases hb : j.val ≤ (((p⁻¹)^k) u).val
    · exact ih hb
    · refine ⟨((p⁻¹)^k) u, Equiv.Perm.SameCycle.pow_right (Equiv.Perm.SameCycle.refl _ _), ?_, ?_⟩
      · omega
      · rw [pow_succ', Equiv.Perm.mul_apply] at hv
        omega

theorem enclosing_cycle_root_star (p : State n) (root u v : Fin n)
    (hu : (p⁻¹).SameCycle root u) (hv : (p⁻¹).SameCycle root v)
    (hinside : ∀ i, (p⁻¹) i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val) :
    RootStar p (fun i => (p.symm i : ℤ)-(i : ℤ)) root := by
  intro i hi
  have hmove : (p⁻¹) i ≠ i := by
    intro hf
    exact hi (by simp [show p.symm i=i from hf])
  obtain ⟨hlo,hhi⟩ := hinside i hmove
  obtain ⟨k,hk⟩ := (hu.symm.trans hv).exists_nat_pow_eq
  obtain ⟨a,ha,hl,hh⟩ := cycle_path_crosses p u i k hlo (by rw [hk]; exact hhi)
  refine ⟨a,i,hu.trans ha,Or.inr ⟨hmove,0,?_,?_⟩,Equiv.Perm.SameCycle.refl _ _⟩
  · have hl' : min (a : ℤ) ((p.symm a : Fin n) : ℤ) ≤ (i : ℤ) := by exact_mod_cast hl
    simpa using hl'
  · have hh' : (i : ℤ) ≤ max (a : ℤ) ((p.symm a : Fin n) : ℤ) := by exact_mod_cast hh
    simpa using hh'

#print axioms enclosing_cycle_root_star
end LRX.PrunedLift
