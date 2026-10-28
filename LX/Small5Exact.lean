import LX.LowerCertificate
import Mathlib

namespace LX.Small5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def potentials : Array ℕ := #[
  0,6,6,7,9,11,6,7,7,2,8,9,7,8,6,9,4,9,7,6,9,10,6,5,
  1,7,7,8,10,11,7,8,7,1,7,8,8,7,7,9,3,8,7,7,8,9,7,5,
  7,9,8,2,8,9,6,8,8,3,9,10,9,8,9,8,3,2,9,4,8,9,8,5,
  7,7,6,10,4,9,10,8,10,9,3,4,6,8,5,10,5,10,9,10,4,3,4,5,
  6,6,7,9,6,5,7,6,8,8,8,5,10,9,6,5,4,5,6,5,8,10,5,4]

def score (p : State 5) : ℕ := potentials[LX.Core.codeIndex (LX.Core.encode p)]!

theorem potential_zero : score 1=0 := by decide +kernel

theorem potential_edges : ∀ c : LX.Core.PermCode 5,∀ a : Letter,
    score (LX.Core.decode c*eval [a]) ≤ score (LX.Core.decode c)+1 := by
  have checked : ∀ c : LX.Core.PermCode 5,
      score (LX.Core.decode c*eval [.l]) ≤ score (LX.Core.decode c)+1 ∧
      score (LX.Core.decode c*eval [.x]) ≤ score (LX.Core.decode c)+1 := by
    decide +kernel
  intro c a
  cases a with
  | l => exact (checked c).1
  | x => exact (checked c).2

noncomputable def farthest : State 5 :=
  Equiv.ofBijective ![1,0,4,2,3] (by decide +kernel)

theorem farthest_score : score farthest=11 := by decide +kernel

theorem diameter_lower : 11 ≤ diameter 5 := by
  have hb := lower_of_code_potential (by decide : 2 ≤ 5) score
    potential_zero potential_edges farthest
  simpa only [farthest_score] using hb


#print axioms diameter_lower
end LX.Small5
