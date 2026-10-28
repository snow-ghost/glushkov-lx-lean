import LX.FiniteCertificate
import Mathlib

-- Generated witnesses; the Lean kernel checks semantics, coverage and length.
namespace LX.Small4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words : Array (List Letter) := #[
  [],
  [.l,.l,.x,.l,.l],
  [.l,.l,.x,.l,.x],
  [.x,.l],
  [.l,.x,.l,.l,.x],
  [.l,.l,.l,.x],
  [.x],
  [.l,.l,.x,.l,.l,.x],
  [.l,.l,.l,.x,.l,.l],
  [.l],
  [.l,.l,.l,.x,.l,.x],
  [.l,.x,.l],
  [.x,.l,.l,.x,.l],
  [.l,.x],
  [.l,.l,.x,.l],
  [.x,.l,.x],
  [.l,.l],
  [.x,.l,.l],
  [.l,.l,.l,.x,.l],
  [.l,.x,.l,.x],
  [.x,.l,.l,.x],
  [.l,.l,.x],
  [.l,.x,.l,.l],
  [.l,.l,.l]]

def table (c : LX.Core.PermCode 4) : List Letter := words[LX.Core.codeIndex c]!

theorem checked : ∀ c : LX.Core.PermCode 4,
    eval (table c)=LX.Core.decode c ∧ (table c).length ≤ 7 := by
  decide +kernel

theorem sharp_words (p : State 4) :
    ∃ w : List Letter,eval w=p ∧ w.length ≤ 7 :=
  words_of_code_certificate table checked p


#print axioms sharp_words
end LX.Small4
