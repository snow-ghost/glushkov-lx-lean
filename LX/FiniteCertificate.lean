import LX.WordMetric
import LRX.PermutationCode

namespace LX

theorem words_of_code_certificate {n B : ℕ} [NeZero n]
    (table : LRX.PermCode n → List Letter)
    (checked : ∀ c,eval (table c)=LRX.decode c ∧ (table c).length ≤ B) :
    ∀ p : State n,∃ w : List Letter,eval w=p ∧ w.length ≤ B := by
  intro p
  obtain ⟨he,hl⟩ := checked (LRX.encode p)
  exact ⟨table (LRX.encode p),by simpa using he,hl⟩

end LX
