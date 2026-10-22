import Mathlib

/-!
The LRX Cayley graph on `Equiv.Perm (Fin n)`. Right multiplication acts
on positions: `L` rotates the list to the left, `R` to the right, and `X`
exchanges its first two entries. The extended diameter avoids the convention
that a disconnected graph has natural-valued diameter zero.
-/
namespace LRX

abbrev State (n : ℕ) := Equiv.Perm (Fin n)

def L (n : ℕ) : State n := finRotate n

def R (n : ℕ) : State n := (L n)⁻¹

def X (n : ℕ) [NeZero n] : State n := Equiv.swap 0 1

def generators (n : ℕ) [NeZero n] : Set (State n) := {L n, R n, X n}

def graph (n : ℕ) [NeZero n] : SimpleGraph (State n) :=
  SimpleGraph.mulCayley (generators n)

inductive Letter where
  | l | r | x
  deriving DecidableEq, Repr

def Letter.eval {n : ℕ} [NeZero n] : Letter → State n
  | .l => L n
  | .r => R n
  | .x => X n

def eval {n : ℕ} [NeZero n] (w : List Letter) : State n :=
  (w.map Letter.eval).prod

@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_cons {n : ℕ} [NeZero n] (a : Letter) (w : List Letter) :
    eval (n := n) (a :: w) = a.eval * eval w := by simp [eval]

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by simp [eval]

theorem Letter.eval_mem {n : ℕ} [NeZero n] (a : Letter) :
    a.eval (n := n) ∈ generators n := by
  cases a <;> simp [Letter.eval, generators]

/-- Left translation is a graph homomorphism for any right Cayley graph. -/
def leftTranslate {G : Type*} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun b := a * b
  map_rel' := by
    intro u v h
    exact (SimpleGraph.mulCayley_adj_mul_iff_right).mpr h

theorem word_edist_le {n : ℕ} [NeZero n] (a : State n) (w : List Letter) :
    (graph n).edist a (a * eval w) ≤ (w.length : ℕ∞) := by
  induction w generalizing a with
  | nil => simp
  | cons c w ih =>
    have step : (graph n).edist a (a * c.eval) ≤ 1 := by
      apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
      by_cases h : a = a * c.eval
      · exact Or.inr h
      · exact Or.inl ((SimpleGraph.mulCayley_adj' _ _ _).mpr
          ⟨h, c.eval, c.eval_mem, Or.inl rfl⟩)
    calc
      (graph n).edist a (a * eval (c :: w)) =
          (graph n).edist a ((a * c.eval) * eval w) := by rw [eval_cons, mul_assoc]
      _ ≤ (graph n).edist a (a * c.eval) +
          (graph n).edist (a * c.eval) ((a * c.eval) * eval w) :=
        SimpleGraph.edist_triangle
      _ ≤ 1 + (w.length : ℕ∞) := add_le_add step (ih _)
      _ = ((c :: w).length : ℕ∞) := by simp [add_comm]

/-- A bounded word for every permutation suffices, without a factor of two. -/
theorem ediam_le_of_words {n B : ℕ} [NeZero n]
    (h : ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ B) :
    (graph n).ediam ≤ (B : ℕ∞) := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro a b
  obtain ⟨w, hw, hlen⟩ := h (a⁻¹ * b)
  have hd := word_edist_le a w
  rw [hw, mul_inv_cancel_left] at hd
  exact hd.trans (by exact_mod_cast hlen)

/-- The exact missing constructive statement for the sharp research bound. -/
def SharpWordBound (n : ℕ) [NeZero n] : Prop :=
  ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ n.choose 2

/-- Conditional transfer only: `SharpWordBound` is not assumed as an axiom. -/
theorem sharp_ediam_of_words {n : ℕ} [NeZero n] (h : SharpWordBound n) :
    (graph n).ediam ≤ (n.choose 2 : ℕ∞) := ediam_le_of_words h

end LRX
