import LRX.FiniteCutLoad
import Mathlib

/-! Displacements and their absolute mass add over disjoint finite cycles. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem displacement_mul (p q : State b) (h : p.Disjoint q) (i : Fin b) :
    displacement (p*q) i=displacement p i+displacement q i := by
  unfold displacement
  rcases h i with hi | hi
  · have hm : (p*q) i=q i := by rw [h.commute.eq]; simp [hi]
    rw [hm,hi]
    ring
  · have hm : (p*q) i=p i := by simp [hi]
    rw [hm,hi]
    ring

theorem abs_displacement_mul (p q : State b) (h : p.Disjoint q) (i : Fin b) :
    |displacement (p*q) i|=|displacement p i|+|displacement q i| := by
  rw [displacement_mul p q h i]
  rcases h i with hi | hi <;> simp [displacement,hi]


end LRX.FiniteCuts
