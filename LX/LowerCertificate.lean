import LRX.PermutationCode
import LX.WordMetric
import Mathlib

namespace LX
variable {n : ℕ} [NeZero n]

/-- A directed potential needs a one-sided inequality for L and X only.
No inequality for the inverse cyclic shift is assumed. -/
theorem potential_word_bound (score : State n → ℕ)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) (w : List Letter) :
    score (p*eval w) ≤ score p+w.length := by
  induction w generalizing p with
  | nil => simp
  | cons a w ih =>
    have he : eval (n := n) (a::w)=eval [a]*eval w := by
      simpa only [List.singleton_append] using eval_append (n := n) [a] w
    rw [he,← mul_assoc]
    have htail := ih (p*eval [a])
    have hhead := hedge p a
    simp only [List.length_cons]
    omega

theorem potential_le_length (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) : score p ≤ length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  have hb := potential_word_bound score hedge 1 w
  simpa only [one_mul,hw,hlen,hzero,zero_add] using hb

theorem potential_le_diameter (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) : score p ≤ diameter n :=
  (potential_le_length hn score hzero hedge p).trans (length_le_diameter p)

/-- Checking edges on surjective permutation codes suffices to certify
the lower bound against every possible word, not just a search output. -/
theorem lower_of_code_potential (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (checked : ∀ c : LRX.PermCode n,∀ a : Letter,
      score (LRX.decode c*eval [a]) ≤ score (LRX.decode c)+1)
    (p : State n) : score p ≤ diameter n := by
  apply potential_le_diameter hn score hzero ?_ p
  intro q a
  simpa only [LRX.decode_encode] using checked (LRX.encode q) a

#print axioms potential_word_bound
#print axioms lower_of_code_potential
end LX
