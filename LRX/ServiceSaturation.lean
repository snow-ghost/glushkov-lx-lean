import LRX.ServiceCertificate
import Mathlib

/-! Finite saturation of real service certificates. Maximality is over finite
sets of labels, not over arbitrary programs. Every reachable cycle is covered. -/
namespace LRX.BufferProgram
variable {n : ℕ} [NeZero n]

def Saturated {p : State n} {d : Fin n → ℤ} (C : ServiceCertificate p d) : Prop :=
  ∀ a : Fin n, (p⁻¹) a ≠ a →
    Visits C.program initialLogical (PeriodicBuffer.contract (n : ℤ) (a : ℤ)) → a ∈ C.labels


/-- Edges are either within a target cycle, or a lifted arrow passing through
a periodic copy of a vertex of a nontrivial target cycle. -/
def ServiceEdge (p : State n) (d : Fin n → ℤ) (i j : Fin n) : Prop :=
  (p⁻¹).SameCycle i j ∨ ((p⁻¹) j ≠ j ∧ ∃ k : ℤ,
    min (i : ℤ) ((i : ℤ)+d i) ≤ (j : ℤ)+k*(n : ℤ) ∧
    (j : ℤ)+k*(n : ℤ) ≤ max (i : ℤ) ((i : ℤ)+d i))


end LRX.BufferProgram
