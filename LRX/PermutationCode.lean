import LRX.Graph

/-! A constructive enumeration of permutations. Checking one word per code
avoids a quadratic search through a finite set of evaluated words. -/
namespace LRX

def PermCode : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin (n + 1) × PermCode n

instance codeFintype : (n : ℕ) → Fintype (PermCode n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := codeFintype n
    exact inferInstanceAs (Fintype (Fin (n + 1) × PermCode n))

def decode : {n : ℕ} → PermCode n → State n
  | 0, _ => 1
  | _ + 1, (i, c) => Equiv.Perm.decomposeFin.symm (i, decode c)

def encode : {n : ℕ} → State n → PermCode n
  | 0, _ => ()
  | _ + 1, p => let q := Equiv.Perm.decomposeFin p; (q.1, encode q.2)

@[simp] theorem decode_encode {n : ℕ} (p : State n) : decode (encode p) = p := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [encode, decode, ih, Prod.mk.eta, Equiv.symm_apply_apply]

def codeIndex : {n : ℕ} → PermCode n → ℕ
  | 0, _ => 0
  | n + 1, (i, c) => i.val * n.factorial + codeIndex c

/-- Exhaustive certification over an explicitly surjective permutation code. -/
theorem words_of_code_certificate {n B : ℕ} [NeZero n]
    (table : PermCode n → List Letter)
    (checked : ∀ c, eval (table c) = decode c ∧ (table c).length ≤ B) :
    ∀ p : State n, ∃ w : List Letter, eval w = p ∧ w.length ≤ B := by
  intro p
  obtain ⟨he, hl⟩ := checked (encode p)
  exact ⟨table (encode p), by simpa using he, hl⟩

end LRX
