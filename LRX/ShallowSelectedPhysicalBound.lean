import LRX.SelectedPhysicalLengths

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State (m+1)} {q : State k}

theorem threshold_physical_bound (B : System P q) (a z : ℕ) (h : B.ReachedThreshold a z)
    (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j) :
    (B.positive.card=a ∧ physicalLength B.positive P (position holes) ≤
      (a : ℤ)*z+(min a z : ℕ)*(∑ j, holes j)) ∨
    (B.negative.card=z ∧ physicalLength B.negative P (position holes) ≤
      (a : ℤ)*z+(min a z : ℕ)*(∑ j, holes j)) := by
  rcases h with h | h
  · left
    refine ⟨h.1,?_⟩
    rw [B.positive_physical_decomposition holes hh]
    have hr := B.positive_rank_capacity
    have hn : (B.negative.card : ℤ)+1 ≤ z := by exact_mod_cast h.2
    rw [h.1] at hr
    have ha : (0 : ℤ) ≤ a := by positivity
    have hs : (∑ j : Fin m, ((B.upward j.val).card : ℤ)*holes j) ≤
        (min a z : ℕ)*(∑ j, holes j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (hh j)
      have hb := (B.cut_count_bounds j.val).1
      have hb' : (B.upward j.val).card ≤ min a z := by omega
      exact_mod_cast hb'
    nlinarith
  · right
    refine ⟨h.1,?_⟩
    rw [B.negative_physical_decomposition holes hh]
    have hr := B.negative_rank_capacity
    have hn : (B.positive.card : ℤ)+1 ≤ a := by exact_mod_cast h.2
    rw [h.1] at hr
    have hz : (0 : ℤ) ≤ z := by positivity
    have hs : (∑ j : Fin m, ((B.downward j.val).card : ℤ)*holes j) ≤
        (min a z : ℕ)*(∑ j, holes j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (hh j)
      have hb := (B.cut_count_bounds j.val).2
      have hb' : (B.downward j.val).card ≤ min a z := by omega
      exact_mod_cast hb'
    nlinarith

def holeMass (f : Fin (m+1) → ℤ) : ℤ := ∑ j : Fin m, (f j.succ-f j.castSucc-1)

theorem holeMass_span (f : Fin (m+1) → ℤ) :
    holeMass f=f (Fin.last m)-f 0-m := by
  have he := placement_from_holes f (Fin.last m)
  simp only [position,Fin.val_last,Fin.is_lt,ite_true] at he
  unfold holeMass
  omega

theorem physical_length_from_holes (S : Finset (Fin (m+1))) (P : State (m+1))
    (f : Fin (m+1) → ℤ) :
    physicalLength S P (position (fun j : Fin m => f j.succ-f j.castSucc-1))=
      physicalLength S P f := by
  apply Finset.sum_congr rfl
  intro x _
  rw [placement_from_holes,placement_from_holes]
  congr 1
  ring

/-- Formula (29) for an arbitrary increasing physical placement. Both the
selected arrows and the contraction trace are constructed in Lean. -/
theorem shallow_selected_physical_bound (P : State (m+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hf : P.support=Finset.univ)
    (f : Fin (m+1) → ℤ) (hmono : StrictMono f)
    (a z : ℕ) (ha : 0 < a) (hz : 0 < z) (hsize : a+z < m+1) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧
      B.selected.card ≤ a+z-1 ∧
      ((B.positive.card=a ∧ physicalLength B.positive P f ≤
          (a : ℤ)*z+(min a z : ℕ)*holeMass f) ∨
       (B.negative.card=z ∧ physicalLength B.negative P f ≤
          (a : ℤ)*z+(min a z : ℕ)*holeMass f)) := by
  obtain ⟨k,q,B,hh,_,_,_,hstop,hcount⟩ := shallow_threshold_trace P hp hs hf a z ha hz hsize
  have hnon : ∀ j : Fin m, 0 ≤ f j.succ-f j.castSucc-1 := by
    intro j
    have hlt := hmono (show j.castSucc < j.succ by simp [Fin.lt_def])
    omega
  have hb := B.threshold_physical_bound a z hstop
    (fun j : Fin m => f j.succ-f j.castSucc-1) hnon
  simp only [physical_length_from_holes] at hb
  exact ⟨k,q,B,hh,hcount,hb⟩

#print axioms shallow_selected_physical_bound
end LRX.ContractionBlocks.System
