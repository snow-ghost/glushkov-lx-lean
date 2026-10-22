import LRX.ProtectedContractionTrace

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State (m+1)} {q : State k}

theorem protected_crossings_empty (B : System P q) (gap : Fin m) (hB : B.Protected gap.val) :
    B.upward gap.val=∅ ∧ B.downward gap.val=∅ := by
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hsel,hlo,hhi⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,_⟩ := (B.selected_iff_internal x).mp hsel
    have ht := B.selected_target_in_block i x hi hsel
    have he := hB i x hi (P x) ht
    omega
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hsel,hlo,hhi⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,_⟩ := (B.selected_iff_internal x).mp hsel
    have ht := B.selected_target_in_block i x hi hsel
    have he := hB i x hi (P x) ht
    omega

theorem weighted_sum_except (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j)
    (count : Fin m → ℕ) (K : ℕ) (hcount : ∀ j, count j ≤ K)
    (gap : Fin m) (hzero : count gap=0) :
    (∑ j, (count j : ℤ)*holes j) ≤ (K : ℤ)*((∑ j, holes j)-holes gap) := by
  have hc := Finset.sum_erase_add (s:=Finset.univ) (f:=fun j => (count j : ℤ)*holes j)
    (Finset.mem_univ gap)
  have hw := Finset.sum_erase_add (s:=Finset.univ) (f:=holes) (Finset.mem_univ gap)
  rw [hzero,Nat.cast_zero,zero_mul,add_zero] at hc
  have hb : (∑ j ∈ Finset.univ.erase gap, (count j : ℤ)*holes j) ≤
      (K : ℤ)*(∑ j ∈ Finset.univ.erase gap, holes j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount j) (hh j)
  rw [hc] at hb
  have he : (∑ j ∈ Finset.univ.erase gap, holes j)=(∑ j, holes j)-holes gap := by omega
  rwa [he] at hb

theorem protected_threshold_physical_bound (B : System P q) (a z : ℕ)
    (h : B.ReachedThreshold a z) (gap : Fin m) (hB : B.Protected gap.val)
    (holes : Fin m → ℤ) (hh : ∀ j, 0 ≤ holes j) :
    (B.positive.card=a ∧ physicalLength B.positive P (position holes) ≤
      (a : ℤ)*z+(min a z : ℕ)*((∑ j, holes j)-holes gap)) ∨
    (B.negative.card=z ∧ physicalLength B.negative P (position holes) ≤
      (a : ℤ)*z+(min a z : ℕ)*((∑ j, holes j)-holes gap)) := by
  have hempty := B.protected_crossings_empty gap hB
  rcases h with h | h
  · left
    refine ⟨h.1,?_⟩
    rw [B.positive_physical_decomposition holes hh]
    have hr := B.positive_rank_capacity
    have hn : (B.negative.card : ℤ)+1 ≤ z := by exact_mod_cast h.2
    rw [h.1] at hr
    have ha : (0 : ℤ) ≤ a := by positivity
    have hs := weighted_sum_except holes hh (fun j : Fin m => (B.upward j.val).card)
      (min a z) (by intro j; have := (B.cut_count_bounds j.val).1; omega) gap
      (by simp [hempty.1])
    nlinarith
  · right
    refine ⟨h.1,?_⟩
    rw [B.negative_physical_decomposition holes hh]
    have hr := B.negative_rank_capacity
    have hn : (B.positive.card : ℤ)+1 ≤ a := by exact_mod_cast h.2
    rw [h.1] at hr
    have hz : (0 : ℤ) ≤ z := by positivity
    have hs := weighted_sum_except holes hh (fun j : Fin m => (B.downward j.val).card)
      (min a z) (by intro j; have := (B.cut_count_bounds j.val).2; omega) gap
      (by simp [hempty.2])
    nlinarith

/-- Protected-hole form of (29). Only the available holes contribute, and
the entire protected history is constructed from original shortness. -/
theorem shallow_protected_physical_bound (P : State (m+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hf : P.support=Finset.univ)
    (f : Fin (m+1) → ℤ) (hmono : StrictMono f)
    (a z : ℕ) (ha : 0 < a) (hz : 0 < z) (hsize : a+z < m+1)
    (gap : Fin m) (h : ℤ) (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (hwide : h < (m : ℤ)+2-a-z+(f gap.succ-f gap.castSucc-1)) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧
      B.Protected gap.val ∧ B.selected.card ≤ a+z-1 ∧
      ((B.positive.card=a ∧ physicalLength B.positive P f ≤
          (a : ℤ)*z+(min a z : ℕ)*(holeMass f-(f gap.succ-f gap.castSucc-1))) ∨
       (B.negative.card=z ∧ physicalLength B.negative P f ≤
          (a : ℤ)*z+(min a z : ℕ)*(holeMass f-(f gap.succ-f gap.castSucc-1)))) := by
  obtain ⟨k,q,B,hh,_,_,_,hprotected,hstop,hcount⟩ :=
    protected_threshold_trace P hp hs hf a z ha hz hsize gap f hmono h hshort hwide
  have hnon : ∀ j : Fin m, 0 ≤ f j.succ-f j.castSucc-1 := by
    intro j
    have hlt := hmono (show j.castSucc < j.succ by simp [Fin.lt_def])
    omega
  have hb := B.protected_threshold_physical_bound a z hstop gap hprotected
    (fun j : Fin m => f j.succ-f j.castSucc-1) hnon
  simp only [physical_length_from_holes] at hb
  exact ⟨k,q,B,hh,hprotected,hcount,hb⟩

#print axioms shallow_protected_physical_bound
end LRX.ContractionBlocks.System
