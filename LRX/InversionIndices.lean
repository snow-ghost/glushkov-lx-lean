import LRX.TraceInversions

/-! Finite copy-index intervals for the inversions of one periodic pair. -/
namespace LRX.LiftedModel
variable {n : ℕ} [NeZero n]

def inversionIndices (q : ℤ) : Finset ℤ :=
  if 0 ≤ q then Finset.Ico (-q) 0 else Finset.Ico 0 (-q)

omit [NeZero n] in
theorem mem_inversion_indices (q k : ℤ) :
    k ∈ inversionIndices q ↔ ¬ ((0 ≤ k) ↔ (-q ≤ k)) := by
  unfold inversionIndices
  split_ifs <;> simp only [Finset.mem_Ico] <;> omega

omit [NeZero n] in
theorem card_inversion_indices (q : ℤ) : (inversionIndices q).card=q.natAbs := by
  unfold inversionIndices
  split_ifs with hq
  · rw [Int.card_Ico]
    simp only [zero_sub, neg_neg]
    have h := Int.toNat_of_nonneg hq
    have ha := Int.natCast_natAbs q
    rw [abs_of_nonneg hq] at ha
    omega
  · rw [Int.card_Ico]
    simp only [sub_zero]
    have h := Int.toNat_of_nonneg (by omega : 0 ≤ -q)
    have ha := Int.natCast_natAbs q
    rw [abs_of_nonpos (by omega : q ≤ 0)] at ha
    omega

omit [NeZero n] in
theorem periodic_order_quotient {N : ℤ} (hN : 0 < N) (a b k : ℤ)
    (hr : (b-a)%N ≠ 0) :
    a < b+N*k ↔ -( (b-a)/N ) ≤ k := by
  have hdiv := Int.ediv_mul_add_emod (b-a) N
  have hr0 := Int.emod_nonneg (b-a) (ne_of_gt hN)
  have hr1 := Int.emod_lt_of_pos (b-a) hN
  have hrpos : 1 ≤ (b-a)%N := by omega
  constructor
  · intro h
    by_contra hbad
    have hk : (b-a)/N+k ≤ -1 := by omega
    nlinarith
  · intro h
    have hk : 0 ≤ (b-a)/N+k := by omega
    nlinarith

theorem position_difference_mod_ne {s : Configuration n} (hs : Aligned s)
    (i j : Fin n) (hij : i ≠ j) : (s.position j-s.position i)%(n : ℤ) ≠ 0 := by
  intro hzero
  have hdiv := Int.ediv_mul_add_emod (s.position j-s.position i) (n : ℤ)
  rw [hzero, add_zero] at hdiv
  apply positions_ne_periodic hs i j hij (-(n : ℤ)*((s.position j-s.position i)/(n : ℤ)))
  · exact dvd_mul_of_dvd_left (dvd_neg.mpr (dvd_refl _)) _
  · nlinarith

theorem initial_pair_order (i j : Fin n) (hij : i < j) (k : ℤ) :
    (i : ℤ) < (j : ℤ)+(n : ℤ)*k ↔ 0 ≤ k := by
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
  have hjn : (j : ℤ) < n := by exact_mod_cast j.isLt
  have hlt : (i : ℤ) < j := by exact_mod_cast hij
  constructor
  · intro h
    by_contra hbad
    have hk : k ≤ -1 := by omega
    nlinarith
  · intro h
    have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith

theorem inversion_index_order {s : Configuration n} (hs : Aligned s)
    (i j : Fin n) (hij : i < j) (k : ℤ) :
    k ∈ inversionIndices ((s.position j-s.position i)/(n : ℤ)) ↔
      ¬ (((i : ℤ) < (j : ℤ)+(n : ℤ)*k) ↔
        s.position i < s.position j+(n : ℤ)*k) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [initial_pair_order i j hij, periodic_order_quotient hn _ _ k
    (position_difference_mod_ne hs i j (ne_of_lt hij)), mem_inversion_indices]

#print axioms card_inversion_indices
#print axioms inversion_index_order
end LRX.LiftedModel
