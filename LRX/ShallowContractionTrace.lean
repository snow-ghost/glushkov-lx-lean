import LRX.ContractionArrowSigns
import LRX.FullSupportShallowStep

namespace LRX.ContractionBlocks.System
variable {m : ℕ} {P : State m}

/-- A trace uses actual adjacent contractions starting at the original cycle. -/
inductive History (P : State m) : {k : ℕ} → (q : State k) → System P q → Prop
  | initial : History P P (System.initial P)
  | step {k : ℕ} {q : State (k+1)} {B : System P q}
      (previous : History P q B) (a : Fin (k+1))
      (hadj : |FiniteCuts.displacement q a|=1) :
      History P (FiniteCuts.contract q a) (B.contract a hadj)

def ReachedThreshold {k : ℕ} {q : State k} (B : System P q) (a z : ℕ) : Prop :=
  (B.positive.card=a ∧ B.negative.card < z) ∨
  (B.negative.card=z ∧ B.positive.card < a)

theorem threshold_selection_bound {k : ℕ} {q : State k} (B : System P q)
    {a z : ℕ} (h : B.ReachedThreshold a z) : B.selected.card ≤ a+z-1 := by
  have hc := B.signs_card
  have hs := B.selected_card
  rcases h with h | h <;> omega

/-- With enough vertices to avoid contracting a two-cycle, one of the two
positive thresholds is reached by a finite trace. -/
theorem reach_threshold_from (a z : ℕ) (hsize : a+z < m) :
    ∀ (k : ℕ) (q : State k) (B : System P q),
    History P q B → q.IsCycle → FiniteCuts.Shallow q → q.support=Finset.univ →
    B.positive.card ≤ a → B.negative.card ≤ z → B.positive.card+B.negative.card < a+z →
    ∃ (t : ℕ) (r : State t) (C : System P r), History P r C ∧ r.IsCycle ∧
      FiniteCuts.Shallow r ∧ r.support=Finset.univ ∧ C.ReachedThreshold a z := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro q B hhist hcycle hshallow hfull hpos hneg hsum
    by_cases hp : B.positive.card=a
    · exact ⟨k,q,B,hhist,hcycle,hshallow,hfull,Or.inl ⟨hp,by omega⟩⟩
    by_cases hn : B.negative.card=z
    · exact ⟨k,q,B,hhist,hcycle,hshallow,hfull,Or.inr ⟨hn,by omega⟩⟩
    have hc := B.signs_card
    have hk : 3 ≤ k := by omega
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨i,hunit,hcy,hs,hf⟩ :=
        FiniteCuts.full_support_shallow_step hcycle hshallow hfull (by omega)
      have hne : q i ≠ i := by
        intro he
        simp [FiniteCuts.displacement,he] at hunit
      have hpc := B.positive_contract_card i hunit hne
      have hnc := B.negative_contract_card i hunit hne
      have hc' := (B.contract i hunit).signs_card
      apply ih k (by omega) (FiniteCuts.contract q i) (B.contract i hunit)
        (History.step hhist i hunit) hcy hs hf
      · split_ifs at hpc <;> omega
      · split_ifs at hnc <;> omega
      · omega

theorem shallow_threshold_trace (P : State m) (hp : P.IsCycle) (hs : FiniteCuts.Shallow P)
    (hf : P.support=Finset.univ) (a z : ℕ) (ha : 0 < a) (hz : 0 < z) (hsize : a+z < m) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧ q.IsCycle ∧
      FiniteCuts.Shallow q ∧ q.support=Finset.univ ∧ B.ReachedThreshold a z ∧
      B.selected.card ≤ a+z-1 := by
  have hc := (initial P).signs_card
  obtain ⟨k,q,B,hh,hcy,hsh,hfull,hstop⟩ :=
    reach_threshold_from a z hsize m P (initial P) (History.initial) hp hs hf
      (by omega) (by omega) (by omega)
  exact ⟨k,q,B,hh,hcy,hsh,hfull,hstop,B.threshold_selection_bound hstop⟩

#print axioms shallow_threshold_trace
end LRX.ContractionBlocks.System
