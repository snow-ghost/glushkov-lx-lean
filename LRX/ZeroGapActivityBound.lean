import LRX.ZeroGapFactorization

/-! The constructed swap factorization bounds the number of active positions
by twice its length, giving an unconditional first inversion reserve. -/
namespace LRX.ZeroGap
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem swap_product_support (factors : List (State n)) (hs : ∀ q ∈ factors, q.IsSwap) :
    factors.prod.support.card ≤ 2*factors.length := by
  induction factors with
  | nil => simp
  | cons q rest ih =>
    have hq := hs q (by simp)
    have hrest := ih (fun s hs' => hs s (by simp [hs']))
    have hcard := Finset.card_le_card (Equiv.Perm.support_mul_le q rest.prod)
    change (q*rest.prod).support.card ≤ (q.support ∪ rest.prod.support).card at hcard
    have hunion := Finset.card_union_le q.support rest.prod.support
    have hqcard := Equiv.Perm.card_support_eq_two.mpr hq
    simp only [List.prod_cons,List.length_cons]
    omega

theorem activity_inversion_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    (p.support.card : ℤ)+2*(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      2*∑ i : Fin n, |d i| := by
  obtain ⟨factors,hprod,hs,hcount⟩ := sorting_transpositions hd hshort
  have hcard := swap_product_support factors hs
  rw [hprod] at hcard
  omega

#print axioms activity_inversion_bound
end LRX.ZeroGap
