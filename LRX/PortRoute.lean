import LRX.LiftedModel
import LRX.RotationWords
import Mathlib

/-! Literal composition of closed services along a paid cursor route. The
permutation product, all letters, and both ends of every move are accounted for. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def rotation (r : Fin n) : State n := L n^r.val

theorem rotation_add (a b : Fin n) : rotation (a+b)=rotation a*rotation b := by
  apply Equiv.ext
  intro i
  simp only [rotation, AffineLift.rotation_power_apply, Fin.cast_val_eq_self, Equiv.Perm.mul_apply]
  abel

theorem rotation_sub (a b : Fin n) : rotation (b-a)=(rotation a)⁻¹*rotation b := by
  have h : rotation a*rotation (b-a)=rotation b := by
    rw [← rotation_add]
    congr 1
    abel
  calc
    rotation (b-a)=(rotation a)⁻¹*(rotation a*rotation (b-a)) := by group
    _ = _ := by rw [h]


structure ClosedService (n : ℕ) [NeZero n] where
  port : Fin n
  word : List Letter
  target : State n
  correct : eval word=(rotation port)⁻¹*target*rotation port
  closed : (word.map LiftedModel.increment).sum=0

def route (s t : Fin n) : List (ClosedService n) → List Letter
  | [] => toPort (t-s)
  | service::rest => toPort (service.port-s) ++ service.word ++ route service.port t rest

def walkCost (s t : Fin n) : List (ClosedService n) → ℕ
  | [] => min (t-s).val (n-(t-s).val)
  | service::rest => min (service.port-s).val (n-(service.port-s).val)+walkCost service.port t rest

def walkOffset (s t : Fin n) : List (ClosedService n) → ℤ
  | [] => shortOffset (t-s)
  | service::rest => shortOffset (service.port-s)+walkOffset service.port t rest


end LRX.RotationWords
