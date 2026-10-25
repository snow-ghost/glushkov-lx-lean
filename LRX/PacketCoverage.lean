import LRX.ServiceSaturation
import Mathlib

/-! A root packet may contain several cycles. Every child is reached directly
from the strongly connected core, followed by movement inside its own cycle. -/
namespace LRX.PrunedLift
variable {n : ℕ}

abbrev Reaches (p : State n) (d : Fin n → ℤ) := Relation.ReflTransGen (BufferProgram.ServiceEdge p d)

def PacketCover (p : State n) (d : Fin n → ℤ) (root : Fin n) : Prop :=
  ∀ i, d i ≠ 0 → ∃ a j,
    Reaches p d root a ∧ Reaches p d a root ∧
    BufferProgram.ServiceEdge p d a j ∧ (p⁻¹).SameCycle j i

def KeepsCore (p : State n) (d : Fin n → ℤ) (root : Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ a, Reaches p d root a → Reaches p d a root → a ∈ S


end LRX.PrunedLift
