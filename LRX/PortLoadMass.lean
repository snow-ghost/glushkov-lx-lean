import LRX.PortLoad

/-! The sum of all actual edge loads equals total absolute token displacement.
This is proved from the integer crossing formula, without a geometric profile
assumption or a bounded displacement hypothesis. -/
namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def signedCrossing (a d r : ℤ) : ℤ := (r-a-d)/(n : ℤ)-(r-a)/(n : ℤ)

theorem quotient_block_sum (m : ℤ) : (∑ r : Fin n, (m+(r : ℤ))/(n : ℤ))=m := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => (m+(r : ℤ))/(n : ℤ)) n]
  exact Int.sum_range_add_ediv m (Nat.pos_of_ne_zero (NeZero.ne n))

theorem signed_crossing_sum (a d : ℤ) :
    (∑ r : Fin n, signedCrossing (n := n) a d (r : ℤ)) = -d := by
  have h1 : (∑ r : Fin n, ((r : ℤ)-a-d)/(n : ℤ)) = -a-d := by
    simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using quotient_block_sum (n := n) (-a-d)
  have h2 : (∑ r : Fin n, ((r : ℤ)-a)/(n : ℤ)) = -a := by
    simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using quotient_block_sum (n := n) (-a)
  simp only [signedCrossing, Finset.sum_sub_distrib, h1, h2]
  ring

omit [NeZero n] in
theorem edge_signed_crossing (a d r : ℤ) :
    PeriodicBuffer.edgePassages (n : ℤ) (a-r) (a-r+d)=|signedCrossing (n := n) a d r| := by
  simp only [PeriodicBuffer.edgePassages, signedCrossing,
    show -(a-r+d)=r-a-d by ring, show -(a-r)=r-a by ring]

theorem single_arrow_load_mass (a d : ℤ) :
    (∑ r : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (a-(r : ℤ)) (a-(r : ℤ)+d))=|d| := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  simp_rw [edge_signed_crossing]
  by_cases hd : 0 ≤ d
  · have hsign (r : Fin n) : signedCrossing (n := n) a d (r : ℤ) ≤ 0 := by
      exact sub_nonpos.mpr (Int.ediv_le_ediv hn (by omega))
    have habs (r : Fin n) := abs_of_nonpos (hsign r)
    simp_rw [habs]
    rw [Finset.sum_neg_distrib, signed_crossing_sum, neg_neg, abs_of_nonneg hd]
  · have hsign (r : Fin n) : 0 ≤ signedCrossing (n := n) a d (r : ℤ) := by
      exact sub_nonneg.mpr (Int.ediv_le_ediv hn (by omega))
    have habs (r : Fin n) := abs_of_nonneg (hsign r)
    simp_rw [habs]
    rw [signed_crossing_sum, abs_of_nonpos (by omega : d ≤ 0)]

theorem port_load_mass (d : Fin n → ℤ) :
    (∑ r : Fin n, portLoad d r)=∑ i : Fin n, |d i| := by
  simp_rw [port_load_original]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => single_arrow_load_mass (i : ℤ) (d i))

omit [NeZero n] in
theorem port_load_nonneg (d : Fin n → ℤ) (r : Fin n) : 0 ≤ portLoad d r := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

#print axioms single_arrow_load_mass
#print axioms port_load_mass
end LRX.RotationWords
