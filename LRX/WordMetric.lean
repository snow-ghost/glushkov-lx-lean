import LRX.Graph

namespace LRX

def Letter.inverse : Letter → Letter
  | .l => .r
  | .r => .l
  | .x => .x

@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]

theorem generator_is_letter {n : ℕ} [NeZero n] {g : State n}
    (hg : g ∈ generators n) : ∃ c : Letter, c.eval = g := by
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨.l, rfl⟩
  · exact ⟨.r, rfl⟩
  · exact ⟨.x, rfl⟩

theorem adj_iff_letter {n : ℕ} [NeZero n] (a b : State n) :
    (graph n).Adj a b ↔ a ≠ b ∧ ∃ c : Letter, a * c.eval = b := by
  rw [graph, SimpleGraph.mulCayley_adj']
  constructor
  · rintro ⟨hne, g, hg, h⟩
    obtain ⟨c, rfl⟩ := generator_is_letter hg
    refine ⟨hne, ?_⟩
    rcases h with h | h
    · exact ⟨c, h⟩
    · refine ⟨c.inverse, ?_⟩
      rw [Letter.eval_inverse, h, mul_inv_cancel_right]
  · rintro ⟨hne, c, hc⟩
    exact ⟨hne, c.eval, c.eval_mem, Or.inl hc⟩

/-- Every graph walk has a literal LRX word of exactly the same length. -/
theorem word_of_walk {n : ℕ} [NeZero n] {a b : State n}
    (p : (graph n).Walk a b) :
    ∃ w : List Letter, a * eval w = b ∧ w.length = p.length := by
  induction p with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons a b d hab p ih =>
    obtain ⟨c, hc⟩ := ((adj_iff_letter a b).mp hab).2
    obtain ⟨w, hw, hlen⟩ := ih
    refine ⟨c :: w, ?_, by simp [hlen]⟩
    rw [eval_cons, ← mul_assoc, hc, hw]

/-- Exact equivalence, useful as the specification for the missing constructor. -/
theorem ediam_le_iff_words {n B : ℕ} [NeZero n] :
    (graph n).ediam ≤ (B : ℕ∞) ↔
      ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ B := by
  constructor
  · intro h p
    have hd : (graph n).edist 1 p ≤ (B : ℕ∞) :=
      SimpleGraph.edist_le_ediam.trans h
    have hfin : (graph n).edist 1 p ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd
    obtain ⟨path, hp⟩ :=
      (SimpleGraph.reachable_of_edist_ne_top hfin).exists_walk_length_eq_edist
    obtain ⟨w, hw, hlen⟩ := word_of_walk path
    refine ⟨w, by simpa using hw, ?_⟩
    have hb : (path.length : ℕ∞) ≤ (B : ℕ∞) := hp ▸ hd
    rw [hlen]
    exact_mod_cast hb
  · exact ediam_le_of_words

/-- The requested all-size theorem, recorded as a proposition, not an axiom. -/
def SharpDiameterTheorem : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → (graph n).ediam ≤ (n.choose 2 : ℕ∞)

theorem sharp_specification : SharpDiameterTheorem ↔
    ∀ (n : ℕ) [NeZero n], 4 ≤ n → SharpWordBound n := by
  simp only [SharpDiameterTheorem, SharpWordBound, ediam_le_iff_words]

end LRX
