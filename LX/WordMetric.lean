import LRX.WordMetric
import LRX.Connected
import LRX.RotationWords

/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX

abbrev State := LRX.State

inductive Letter where
  | l | x
  deriving DecidableEq, Repr

def Letter.toLRX : Letter → LRX.Letter
  | .l => .l
  | .x => .x

def eval {n : ℕ} [NeZero n] (w : List Letter) : State n :=
  LRX.eval (w.map Letter.toLRX)

@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]

/-- A correctness bridge only: expanding R this way does not prove a quadratic bound. -/
def expandLetter (n : ℕ) : LRX.Letter → List Letter
  | .l => [.l]
  | .r => List.replicate (n - 1) .l
  | .x => [.x]

def expand (n : ℕ) (w : List LRX.Letter) : List Letter :=
  w.flatMap (expandLetter n)

theorem expandLetter_eval {n : ℕ} [NeZero n] (c : LRX.Letter) :
    eval (expandLetter n c) = c.eval (n := n) := by
  cases c with
  | l => simp [expandLetter, eval, Letter.toLRX, LRX.eval, LRX.Letter.eval]
  | x => simp [expandLetter, eval, Letter.toLRX, LRX.eval, LRX.Letter.eval]
  | r =>
    have hn : 0 < n := NeZero.pos n
    have hp := LRX.RotationWords.rotation_period (n := n)
    have he : LRX.L n ^ (n - 1) * LRX.L n = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hn, hp]
    have hi : LRX.L n ^ (n - 1) = (LRX.L n)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left he
    simpa [expandLetter, eval, Letter.toLRX, LRX.eval, LRX.Letter.eval, LRX.R] using hi

theorem expand_eval {n : ℕ} [NeZero n] (w : List LRX.Letter) :
    eval (expand n w) = LRX.eval (n := n) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change eval (expandLetter n c ++ expand n w) = _
    rw [eval_append, expandLetter_eval, ih, LRX.eval_cons]

theorem exists_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p := by
  obtain ⟨path⟩ := LRX.connected n hn 1 p
  obtain ⟨w, hw, _⟩ := LRX.word_of_walk path
  exact ⟨expand n w, by simpa [expand_eval] using hw⟩

/-- Minimum directed length from the identity; reachability is proved separately. -/
noncomputable def length {n : ℕ} [NeZero n] (p : State n) : ℕ :=
  sInf {k : ℕ | ∃ w : List Letter, eval w = p ∧ w.length = k}

theorem length_le_word {n : ℕ} [NeZero n] (w : List Letter) :
    length (eval (n := n) w) ≤ w.length := by
  exact Nat.sInf_le ⟨w, rfl, rfl⟩

theorem exists_shortest_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p ∧ w.length = length p := by
  obtain ⟨w, hw⟩ := exists_word hn p
  exact Nat.sInf_mem (show Set.Nonempty {k : ℕ | ∃ w : List Letter,
    eval w = p ∧ w.length = k} from ⟨w.length, w, hw, rfl⟩)

/-- Right-multiplication directed distance, without symmetrizing generators. -/
noncomputable def dist {n : ℕ} [NeZero n] (a b : State n) : ℕ := length (a⁻¹ * b)

/-- Maximum directed distance; translation reduces all pairs to the identity. -/
noncomputable def diameter (n : ℕ) [NeZero n] : ℕ :=
  Finset.univ.sup (fun p : State n => length p)

theorem length_le_diameter {n : ℕ} [NeZero n] (p : State n) :
    length p ≤ diameter n := Finset.le_sup (f := fun p : State n => length p) (Finset.mem_univ p)

theorem diameter_le_iff_words {n B : ℕ} [NeZero n] (hn : 2 ≤ n) :
    diameter n ≤ B ↔ ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ B := by
  constructor
  · intro h p
    obtain ⟨w, hw, hl⟩ := exists_shortest_word hn p
    exact ⟨w, hw, hl ▸ (length_le_diameter p).trans h⟩
  · intro h
    apply Finset.sup_le
    intro p _
    obtain ⟨w, hw, hl⟩ := h p
    exact (hw ▸ length_le_word w).trans hl

theorem dist_le_diameter {n : ℕ} [NeZero n] (a b : State n) :
    dist a b ≤ diameter n := length_le_diameter _

theorem diameter_lt_iff_words {n : ℕ} [NeZero n] (hn : 2 ≤ n) (B : ℚ) :
    (diameter n : ℚ) < B ↔
      ∀ p : State n, ∃ w : List Letter, eval w = p ∧ (w.length : ℚ) < B := by
  constructor
  · intro h p
    obtain ⟨w, hw, hl⟩ := exists_shortest_word hn p
    refine ⟨w, hw, ?_⟩
    rw [hl]
    exact lt_of_le_of_lt (by exact_mod_cast length_le_diameter p) h
  · intro h
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (State n)) ⟨1, Finset.mem_univ _⟩ length
    obtain ⟨w, hw, hl⟩ := h p
    have he : diameter n = length p := hp
    rw [he]
    exact lt_of_le_of_lt (by exact_mod_cast hw ▸ length_le_word w) hl

/-- Exact rational specification of the requested bound, with C uniform in n. -/
def QuadraticUpperBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) [NeZero n], 4 ≤ n →
    (diameter n : ℚ) < (3 * (n : ℚ)^2 - 8 * n) / 4 + C

/-- Integer word-price formulation; subtraction never takes place in ℕ. -/
def QuadraticWordBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) [NeZero n], 4 ≤ n → ∀ p : State n,
    ∃ w : List Letter, eval w = p ∧
      4 * (w.length : ℤ) < 3 * (n : ℤ)^2 - 8 * n + 4 * C

theorem quadratic_specification : QuadraticUpperBound ↔ QuadraticWordBound := by
  constructor
  · rintro ⟨C, h⟩
    refine ⟨C, ?_⟩
    intro n _ hn p
    obtain ⟨w, hw, hl⟩ := (diameter_lt_iff_words (by omega : 2 ≤ n) _).mp (h n hn) p
    refine ⟨w, hw, ?_⟩
    have hh : 4 * (w.length : ℚ) < 3 * (n : ℚ)^2 - 8 * n + 4 * C := by linarith
    exact_mod_cast hh
  · rintro ⟨C, h⟩
    refine ⟨C, ?_⟩
    intro n _ hn
    apply (diameter_lt_iff_words (by omega : 2 ≤ n) _).mpr
    intro p
    obtain ⟨w, hw, hl⟩ := h n hn p
    refine ⟨w, hw, ?_⟩
    have hh : 4 * (w.length : ℚ) < 3 * (n : ℚ)^2 - 8 * n + 4 * C := by exact_mod_cast hl
    linarith

#print axioms expand_eval
#print axioms exists_shortest_word
#print axioms diameter_le_iff_words
#print axioms quadratic_specification
end LX
