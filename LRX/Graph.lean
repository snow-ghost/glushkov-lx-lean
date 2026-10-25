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


/-- The exact missing constructive statement for the sharp research bound. -/
def SharpWordBound (n : ℕ) [NeZero n] : Prop :=
  ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ n.choose 2


end LRX
