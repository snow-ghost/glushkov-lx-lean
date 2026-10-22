import LRX.DominantHoleSelection

namespace LRX.AffineLift
open scoped BigOperators
variable {n r : ℕ}

theorem majorized_injective_subset {d : Fin n → ℤ} (hm : Majorized d)
    (e : Fin r ↪ Fin n) (S : Finset (Fin r)) :
    2*(∑ i ∈ S, d (e i)) ≤ (S.card : ℤ)*(n-S.card) := by
  have h := hm (S.image e)
  rw [Finset.card_image_of_injective _ e.injective,
    Finset.sum_image (fun i _ j _ hij => e.injective hij)] at h
  exact h

/-- Apply ambient capacity only to the original arrows left after selection. -/
theorem selected_positive_residual (δ : Fin r → ℤ) (hbalance : ∑ i, δ i=0)
    (hcap : ∀ T : Finset (Fin r), 2*(∑ i ∈ T, δ i) ≤ (T.card : ℤ)*(n-T.card))
    (S : Finset (Fin r)) (hS : S ⊆ Finset.univ.filter (fun i => 0 < δ i)) :
    (∑ i, |δ i|) ≤ 2*(∑ i ∈ S, |δ i|)+
      (((Finset.univ.filter (fun i => 0 < δ i)) \ S).card : ℤ)*
        (n-((Finset.univ.filter (fun i => 0 < δ i)) \ S).card) := by
  let T := Finset.univ.filter (fun i => 0 < δ i)
  have he := subset_displacement_balance δ Finset.univ hbalance
  have hs := Finset.sum_sdiff (f:=δ) hS
  have hc := hcap (T \ S)
  have ha : (∑ i ∈ S, |δ i|)=∑ i ∈ S, δ i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_pos (Finset.mem_filter.mp (hS hi)).2
  change (∑ i, |δ i|)=2*(∑ i ∈ T, δ i) at he
  change (∑ i ∈ T \ S, δ i)+(∑ i ∈ S, δ i)=∑ i ∈ T, δ i at hs
  change (∑ i, |δ i|) ≤ 2*(∑ i ∈ S, |δ i|)+( ((T \ S).card : ℤ)*(n-(T \ S).card))
  rw [ha]
  linarith

theorem original_selected_positive_residual {d : Fin n → ℤ} (hm : Majorized d)
    (e : Fin r ↪ Fin n) (δ : Fin r → ℤ) (hδ : ∀ i, d (e i)=δ i)
    (hbalance : ∑ i, δ i=0) (S : Finset (Fin r))
    (hS : S ⊆ Finset.univ.filter (fun i => 0 < δ i)) :
    (∑ i, |δ i|) ≤ 2*(∑ i ∈ S, |δ i|)+
      (((Finset.univ.filter (fun i => 0 < δ i)) \ S).card : ℤ)*
        (n-((Finset.univ.filter (fun i => 0 < δ i)) \ S).card) := by
  apply selected_positive_residual δ hbalance _ S hS
  intro T
  simpa only [hδ] using majorized_injective_subset hm e T

theorem original_selected_negative_residual {d : Fin n → ℤ}
    (hd : ∑ i, d i=0) (hm : Majorized d)
    (e : Fin r ↪ Fin n) (δ : Fin r → ℤ) (hδ : ∀ i, d (e i)=δ i)
    (hbalance : ∑ i, δ i=0) (S : Finset (Fin r))
    (hS : S ⊆ Finset.univ.filter (fun i => δ i < 0)) :
    (∑ i, |δ i|) ≤ 2*(∑ i ∈ S, |δ i|)+
      (((Finset.univ.filter (fun i => δ i < 0)) \ S).card : ℤ)*
        (n-((Finset.univ.filter (fun i => δ i < 0)) \ S).card) := by
  have hb : (∑ i, -δ i)=0 := by rw [Finset.sum_neg_distrib,hbalance,neg_zero]
  have he := original_selected_positive_residual (majorized_neg hd hm) e
    (fun i => -δ i) (fun i => by simp only [hδ]) hb S (by simpa using hS)
  simpa only [abs_neg,neg_pos] using he

#print axioms original_selected_negative_residual
#print axioms original_selected_positive_residual
end LRX.AffineLift
