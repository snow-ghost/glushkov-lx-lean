import LRX.ProtectedShallowStep

namespace LRX.ContractionBlocks.System
variable {m : ℕ} {P : State (m+1)}

/-- Original shortness and the worst pre-stop block count justify every
protected step; absence of extreme arrows is derived, never assumed. -/
theorem reach_protected_threshold_from (a z : ℕ) (hsize : a+z < m+1)
    (gap : Fin m) (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (hwide : h < (m : ℤ)+2-a-z+(f gap.succ-f gap.castSucc-1)) :
    ∀ (k : ℕ) (q : State k) (B : System P q),
    History P q B → q.IsCycle → FiniteCuts.Shallow q → q.support=Finset.univ →
    B.Protected gap.val →
    B.positive.card ≤ a → B.negative.card ≤ z → B.positive.card+B.negative.card < a+z →
    ∃ (t : ℕ) (r : State t) (C : System P r), History P r C ∧ r.IsCycle ∧
      FiniteCuts.Shallow r ∧ r.support=Finset.univ ∧ C.Protected gap.val ∧ C.ReachedThreshold a z := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro q B hhist hcycle hshallow hfull hprotected hpos hneg hsum
    by_cases hp : B.positive.card=a
    · exact ⟨k,q,B,hhist,hcycle,hshallow,hfull,hprotected,Or.inl ⟨hp,by omega⟩⟩
    by_cases hn : B.negative.card=z
    · exact ⟨k,q,B,hhist,hcycle,hshallow,hfull,hprotected,Or.inr ⟨hn,by omega⟩⟩
    have hc := B.signs_card
    have hk : 3 ≤ k := by omega
    cases k with
    | zero => omega
    | succ k =>
      have hw : h < (k : ℤ)+(f gap.succ-f gap.castSucc-1) := by omega
      obtain ⟨i,hunit,hchosen⟩ := B.protected_shallow_unit hcycle hshallow hfull
        gap hprotected (by omega) f hf h hshort hw
      have hcard : 3 ≤ q.support.card := by simpa [hfull] using hk
      obtain ⟨hcy,hs⟩ := FiniteCuts.contract_shallow_cycle hcycle hcard hshallow i hunit
      have hdrop := FiniteCuts.contract_cycle_support_card hcycle hcard i hunit
      have hfull' : (FiniteCuts.contract q i).support=Finset.univ := by
        apply Finset.eq_univ_of_card
        have hcard' : q.support.card=k+1 := by simp [hfull]
        simpa using (show (FiniteCuts.contract q i).support.card=k by omega)
      have hne : q i ≠ i := by
        intro he
        simp [FiniteCuts.displacement,he] at hunit
      have hpc := B.positive_contract_card i hunit hne
      have hnc := B.negative_contract_card i hunit hne
      have hc' := (B.contract i hunit).signs_card
      apply ih k (by omega) (FiniteCuts.contract q i) (B.contract i hunit)
        (History.step hhist i hunit) hcy hs hfull'
        (B.contract_protected i hunit gap.val hprotected hchosen)
      · split_ifs at hpc <;> omega
      · split_ifs at hnc <;> omega
      · omega

theorem protected_threshold_trace (P : State (m+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hf : P.support=Finset.univ)
    (a z : ℕ) (ha : 0 < a) (hz : 0 < z) (hsize : a+z < m+1)
    (gap : Fin m) (f : Fin (m+1) → ℤ) (hmono : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (hwide : h < (m : ℤ)+2-a-z+(f gap.succ-f gap.castSucc-1)) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧ q.IsCycle ∧
      FiniteCuts.Shallow q ∧ q.support=Finset.univ ∧ B.Protected gap.val ∧
      B.ReachedThreshold a z ∧ B.selected.card ≤ a+z-1 := by
  have hc := (initial P).signs_card
  obtain ⟨k,q,B,hh,hcy,hsh,hfull,hprotected,hstop⟩ :=
    reach_protected_threshold_from a z hsize gap f hmono h hshort hwide
      (m+1) P (initial P) History.initial hp hs hf (initial_protected P gap.val)
      (by omega) (by omega) (by omega)
  exact ⟨k,q,B,hh,hcy,hsh,hfull,hprotected,hstop,B.threshold_selection_bound hstop⟩

#print axioms protected_threshold_trace
end LRX.ContractionBlocks.System
