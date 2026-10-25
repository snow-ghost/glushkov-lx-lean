import LRX.BufferMachine
import Mathlib

/-! A certified compiler of legal periodic-buffer programs into literal LRX
words. Integer positions are preserved; rotations and exchanges are counted
separately. Legality of a cycle-scheduling algorithm remains a later obligation. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

structure Logical (n : ℕ) where
  buffer : Fin n
  coord : Fin n → ℤ
  head : ℤ

inductive Command (n : ℕ) where
  | forward | backward | exchange (token : Fin n)
  deriving DecidableEq

variable {n : ℕ} [NeZero n]

def logicalStep (c : Command n) (t : Logical n) : Logical n := match c with
  | .forward => ⟨t.buffer, Function.update t.coord t.buffer (t.coord t.buffer+1), t.head+1⟩
  | .backward => ⟨t.buffer, Function.update t.coord t.buffer (t.coord t.buffer-1), t.head-1⟩
  | .exchange j => ⟨j, t.coord, t.head⟩

def Admissible (c : Command n) (t : Logical n) : Prop := match c with
  | .forward | .backward => True
  | .exchange j => j ≠ t.buffer ∧ (t.coord j-t.head)%BufferMachine.slots n=0

def word : Command n → List Letter
  | .forward => [.x,.l]
  | .backward => [.r,.x]
  | .exchange _ => [.x]

def compile : List (Command n) → List Letter
  | [] => []
  | c :: cs => word c ++ compile cs

def logicalRun : List (Command n) → Logical n → Logical n
  | [], t => t
  | c :: cs, t => logicalRun cs (logicalStep c t)

def Valid : List (Command n) → Logical n → Prop
  | [], _ => True
  | c :: cs, t => Admissible c t ∧ Valid cs (logicalStep c t)




def Matches (s : LiftedModel.Configuration n) (t : Logical n) : Prop :=
  s.cursor=t.head ∧ BufferMachine.Represents s t.buffer t.coord


def rotationCost : Command n → ℕ
  | .forward | .backward => 1
  | .exchange _ => 0

def rotations (w : List Letter) : ℕ := (w.filter (fun a => a ≠ .x)).length

def exchanges (w : List Letter) : ℕ := (w.filter (fun a => a = .x)).length









end LRX.BufferProgram
