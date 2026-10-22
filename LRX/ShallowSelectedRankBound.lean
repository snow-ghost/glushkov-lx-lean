import LRX.ShallowContractionTrace
import LRX.ContractionSelectedCapacity

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

def rankLength (S : Finset (Fin m)) (P : State m) : ℤ :=
  ∑ x ∈ S, |(P x : ℤ)-(x : ℤ)|

theorem positive_rank_capacity (B : System P q) :
    rankLength B.positive P ≤ (B.positive.card : ℤ)*(B.negative.card+1) := by
  have hsub : B.positive ⊆ B.selected := Finset.filter_subset _ _
  have hc := B.selected_difference_capacity B.positive hsub
  have hs := B.signs_card
  have hsel := B.selected_card
  have hrest : (B.selected \ B.positive).card=B.negative.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  rw [hrest] at hc
  have he : rankLength B.positive P=∑ x ∈ B.positive, ((P x : ℤ)-(x : ℤ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    exact abs_of_nonneg (by omega)
  rwa [he]

theorem negative_rank_capacity (B : System P q) :
    rankLength B.negative P ≤ (B.negative.card : ℤ)*(B.positive.card+1) := by
  have hsub : B.negative ⊆ B.selected := Finset.filter_subset _ _
  have hc := B.selected_reverse_difference_capacity B.negative hsub
  have hs := B.signs_card
  have hsel := B.selected_card
  have hrest : (B.selected \ B.negative).card=B.positive.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  rw [hrest] at hc
  have he : rankLength B.negative P=∑ x ∈ B.negative, ((x : ℤ)-(P x : ℤ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    rw [abs_of_nonpos (by omega)]
    ring
  rwa [he]

theorem threshold_rank_bound (B : System P q) (a z : ℕ) (h : B.ReachedThreshold a z) :
    (B.positive.card=a ∧ rankLength B.positive P ≤ (a : ℤ)*z) ∨
    (B.negative.card=z ∧ rankLength B.negative P ≤ (a : ℤ)*z) := by
  rcases h with h | h
  · left
    refine ⟨h.1,?_⟩
    have hc := B.positive_rank_capacity
    rw [h.1] at hc
    have hz : (B.negative.card : ℤ)+1 ≤ z := by exact_mod_cast h.2
    have ha : (0 : ℤ) ≤ a := by positivity
    nlinarith
  · right
    refine ⟨h.1,?_⟩
    have hc := B.negative_rank_capacity
    rw [h.1] at hc
    have ha : (B.positive.card : ℤ)+1 ≤ a := by exact_mod_cast h.2
    have hz : (0 : ℤ) ≤ z := by positivity
    nlinarith

/-- The rank part of (29), with an actual contraction history and actual
original arrows, obtained directly from the event-graph shallow neighbor lemma. -/
theorem shallow_selected_rank_bound (P : State m) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hf : P.support=Finset.univ)
    (a z : ℕ) (ha : 0 < a) (hz : 0 < z) (hsize : a+z < m) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧
      B.selected.card ≤ a+z-1 ∧
      ((B.positive.card=a ∧ rankLength B.positive P ≤ (a : ℤ)*z) ∨
       (B.negative.card=z ∧ rankLength B.negative P ≤ (a : ℤ)*z)) := by
  obtain ⟨k,q,B,hh,_,_,_,hstop,hcount⟩ := shallow_threshold_trace P hp hs hf a z ha hz hsize
  exact ⟨k,q,B,hh,hcount,B.threshold_rank_bound a z hstop⟩

#print axioms shallow_selected_rank_bound
end LRX.ContractionBlocks.System
