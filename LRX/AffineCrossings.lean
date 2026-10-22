import LRX.PeriodicLift

/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LRX.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h

theorem lift_residue {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    i + (d i : Fin n) = p.symm i + (c : Fin n) := by
  have h := cast_eq_of_modEq (hd.2 i)
  simpa using h

def crossingNumerator (d : Fin n → ℤ) (i j : Fin n) : ℤ :=
  ((j - i : Fin n) : ℤ) + d j - d i

def crossing (d : Fin n → ℤ) (i j : Fin n) : ℤ :=
  -(crossingNumerator d i j / (n : ℤ))

theorem numerator_cast {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i j : Fin n) :
    (crossingNumerator d i j : Fin n) = p.symm j - p.symm i := by
  simp only [crossingNumerator, Int.cast_sub, Int.cast_add]
  simp only [Int.cast_natCast, Fin.cast_val_eq_self]
  calc
    j - i + (d j : Fin n) - (d i : Fin n) =
        (j + (d j : Fin n)) - (i + (d i : Fin n)) := by abel
    _ = (p.symm j + (c : Fin n)) - (p.symm i + (c : Fin n)) := by
      rw [lift_residue hd j, lift_residue hd i]
    _ = p.symm j - p.symm i := by abel

theorem numerator_remainder {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i j : Fin n) :
    crossingNumerator d i j % (n : ℤ) = ((p.symm j - p.symm i : Fin n) : ℤ) := by
  have h := congrArg (fun a : Fin n => (a : ℤ)) (numerator_cast hd i j)
  have hz : ((crossingNumerator d i j : Fin n) : ℤ) = crossingNumerator d i j % (n : ℤ) := by
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    simpa only [Fin.val_intCast] using
      Int.toNat_of_nonneg (Int.emod_nonneg (crossingNumerator d i j) hn0)
  exact hz.symm.trans h

theorem numerator_sum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    ∑ j, crossingNumerator d i j = (∑ j : Fin n, (j : ℤ)) - (n : ℤ) * d i := by
  have hshift := Equiv.sum_comp (Equiv.subRight i) (fun j : Fin n => (j : ℤ))
  change (∑ j : Fin n, ((j - i : Fin n) : ℤ)) = ∑ j : Fin n, (j : ℤ) at hshift
  simp only [crossingNumerator, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hshift, hd.1]
  simp

theorem remainder_sum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    ∑ j, crossingNumerator d i j % (n : ℤ) = ∑ j : Fin n, (j : ℤ) := by
  simp_rw [numerator_remainder hd]
  exact Equiv.sum_comp (p.symm.trans (Equiv.subRight (p.symm i)))
    (fun j : Fin n => (j : ℤ))

/-- Net signed crossings of a token equal its exact integer displacement. -/
theorem crossing_row_sum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) : ∑ j, crossing d i j = d i := by
  have hdiv : (n : ℤ) * (∑ j, crossingNumerator d i j / (n : ℤ)) +
      (∑ j, crossingNumerator d i j % (n : ℤ)) = ∑ j, crossingNumerator d i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Int.mul_ediv_add_emod _ _
  rw [remainder_sum hd, numerator_sum hd] at hdiv
  have he : (∑ j, crossingNumerator d i j / (n : ℤ)) = -d i := by
    apply (mul_left_cancel₀ (ne_of_gt (modulus_pos (n := n))))
    linarith [hdiv]
  simp only [crossing, Finset.sum_neg_distrib, he, neg_neg]


theorem cyclic_difference_sum (i j : Fin n) (hij : i ≠ j) :
    ((j - i : Fin n) : ℤ) + ((i - j : Fin n) : ℤ) = (n : ℤ) := by
  have hne : j - i ≠ (0 : Fin n) := sub_ne_zero.mpr hij.symm
  have he : i - j = -(j - i) := by abel
  rw [he]
  change ((j-i).val : ℤ) + ((-(j-i)).val : ℤ) = _
  rw [Fin.val_neg, ite_eq_right hne]
  have hlt := (j-i).isLt
  omega

@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]

theorem crossing_antisymm {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i j : Fin n) : crossing d i j = -crossing d j i := by
  by_cases hij : i = j
  · subst j; simp
  have hnum : crossingNumerator d i j + crossingNumerator d j i = (n : ℤ) := by
    have h := cyclic_difference_sum i j hij
    dsimp [crossingNumerator]
    linarith
  have hrem : crossingNumerator d i j % (n : ℤ) +
      crossingNumerator d j i % (n : ℤ) = (n : ℤ) := by
    rw [numerator_remainder hd, numerator_remainder hd]
    exact cyclic_difference_sum (p.symm i) (p.symm j) (fun h => hij (p.symm.injective h))
  have hi := Int.mul_ediv_add_emod (crossingNumerator d i j) (n : ℤ)
  have hj := Int.mul_ediv_add_emod (crossingNumerator d j i) (n : ℤ)
  have hz : (n : ℤ) * (crossingNumerator d i j / (n : ℤ) +
      crossingNumerator d j i / (n : ℤ)) = 0 := by nlinarith
  have hq := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (modulus_pos (n := n)))
  dsimp [crossing]
  omega


/-- In a majorized lift, each signed pair crossing is -1, 0 or 1. -/
theorem crossing_unit {d : Fin n → ℤ} (hd : ∑ i, d i = 0)
    (hm : Majorized d) (i j : Fin n) : |crossing d i j| ≤ 1 := by
  have hab := range_bound hd hm i j
  have hba := range_bound hd hm j i
  have hlo : (0 : ℤ) ≤ ((j-i : Fin n) : ℤ) := by omega
  have hhi : ((j-i : Fin n) : ℤ) < n := by exact_mod_cast (j-i).isLt
  have hnumlo : -(n : ℤ) ≤ crossingNumerator d i j := by
    dsimp [crossingNumerator]; omega
  have hnumhi : crossingNumerator d i j < 2 * (n : ℤ) := by
    dsimp [crossingNumerator]; omega
  have hqlo : -1 ≤ crossingNumerator d i j / (n : ℤ) :=
    (Int.le_ediv_iff_mul_le (modulus_pos (n := n))).mpr (by simpa using hnumlo)
  have hqhi : crossingNumerator d i j / (n : ℤ) < 2 :=
    (Int.ediv_lt_iff_lt_mul (modulus_pos (n := n))).mpr hnumhi
  rw [abs_le]
  dsimp [crossing]
  omega

#print axioms crossing_row_sum
#print axioms crossing_antisymm
#print axioms crossing_unit
end LRX.AffineLift
