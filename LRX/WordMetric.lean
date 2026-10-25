import LRX.Graph
import Mathlib

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


/-- The requested all-size theorem, recorded as a proposition, not an axiom. -/
def SharpDiameterTheorem : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → (graph n).ediam ≤ (n.choose 2 : ℕ∞)


end LRX
