import LX.GreedyRotationOptimality
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem paid_rotations_phase (c : Fin n) (g : List Letter) :
    (paidRotations c g : Fin n)=c := by
  simp only [paidRotations,Nat.cast_add,Fin.cast_val_eq_self]
  ring

theorem phase_order_gap (c : Fin n) (u v : ℕ) (hu : (u : Fin n)=c)
    (hv : (v : Fin n)=c) (hlt : u < v) : u+n ≤ v := by
  have hu' : u % n=c.val := by have h := congrArg Fin.val hu; simpa using h
  have hv' : v % n=c.val := by have h := congrArg Fin.val hv; simpa using h
  have hd := Nat.mod_add_div u n
  have he := Nat.mod_add_div v n
  have hnpos := NeZero.pos n
  have hq : u/n+1 ≤ v/n := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left n (show v/n ≤ u/n by omega)
    omega
  have hm := Nat.mul_le_mul_left n hq
  rw [Nat.mul_add,Nat.mul_one] at hm
  omega

/-- Last cursor in this phase that could still give a price below B. -/
def lowerDeadline (n I B c : ℕ) : ℕ := c+n*((B-I-1-c)/n)


/-- A computable certificate: either the starting phase already costs
enough, or the greedy board is nonzero at the last affordable cursor. -/
def LowerDeadlineCertificate (B : ℕ) (c : Fin n) (d : Fin n → ℤ) : Prop :=
  B ≤ inversions d+c.val ∨
    ¬∀ i,saturatedSweep d (lowerDeadline n (inversions d) B c.val) i=0


end LX.AffineScan

namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]


end LX
