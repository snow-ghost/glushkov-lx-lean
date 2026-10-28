import LX.PermutationCode
import LX.WordMetric
import Mathlib

namespace LX

theorem words_of_code_certificate {n B : ℕ} [NeZero n]
    (table : LX.Core.PermCode n → List Letter)
    (checked : ∀ c,eval (table c)=LX.Core.decode c ∧ (table c).length ≤ B) :
    ∀ p : State n,∃ w : List Letter,eval w=p ∧ w.length ≤ B := by
  intro p
  obtain ⟨he,hl⟩ := checked (LX.Core.encode p)
  exact ⟨table (LX.Core.encode p),by simpa using he,hl⟩

end LX
