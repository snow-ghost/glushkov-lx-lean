import LRX.ContractionCutFlux
import LRX.ShallowSelectedRankBound

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

def upward (B : System P q) (gap : ℕ) : Finset (Fin m) :=
  B.selected.filter (fun x => x.val ≤ gap ∧ gap < (P x).val)

def downward (B : System P q) (gap : ℕ) : Finset (Fin m) :=
  B.selected.filter (fun x => (P x).val ≤ gap ∧ gap < x.val)

theorem upward_subset_positive (B : System P q) (gap : ℕ) : B.upward gap ⊆ B.positive := by
  intro x hx
  obtain ⟨hsel,h1,h2⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hsel,by omega⟩

theorem downward_subset_negative (B : System P q) (gap : ℕ) : B.downward gap ⊆ B.negative := by
  intro x hx
  obtain ⟨hsel,h1,h2⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hsel,by omega⟩

theorem cut_flux_counts (B : System P q) (gap : ℕ) :
    (∑ x ∈ B.selected, (rightOf gap (P x)-rightOf gap x)) =
      ((B.upward gap).card : ℤ)-(B.downward gap).card := by
  have point : ∀ x : Fin m, rightOf gap (P x)-rightOf gap x =
      (if x.val ≤ gap ∧ gap < (P x).val then (1 : ℤ) else 0) -
      (if (P x).val ≤ gap ∧ gap < x.val then (1 : ℤ) else 0) := by
    intro x
    simp only [rightOf]
    split_ifs <;> omega
  simp only [point,Finset.sum_sub_distrib]
  simp [upward,downward,Finset.sum_boole]

theorem cut_count_bounds (B : System P q) (gap : ℕ) :
    (B.upward gap).card ≤ min B.positive.card (B.negative.card+1) ∧
    (B.downward gap).card ≤ min B.negative.card (B.positive.card+1) := by
  have hu := Finset.card_le_card (B.upward_subset_positive gap)
  have hd := Finset.card_le_card (B.downward_subset_negative gap)
  have hf := B.selected_cut_flux_bound gap
  rw [B.cut_flux_counts gap] at hf
  simp only [abs_eq_max_neg] at hf
  omega

theorem threshold_cut_bounds (B : System P q) (a z : ℕ) (h : B.ReachedThreshold a z) :
    (B.positive.card=a ∧ ∀ gap, (B.upward gap).card ≤ min a z) ∨
    (B.negative.card=z ∧ ∀ gap, (B.downward gap).card ≤ min a z) := by
  rcases h with h | h
  · left
    refine ⟨h.1,?_⟩
    intro gap
    have hc := (B.cut_count_bounds gap).1
    omega
  · right
    refine ⟨h.1,?_⟩
    intro gap
    have hc := (B.cut_count_bounds gap).2
    omega

#print axioms cut_count_bounds
#print axioms threshold_cut_bounds
end LRX.ContractionBlocks.System
