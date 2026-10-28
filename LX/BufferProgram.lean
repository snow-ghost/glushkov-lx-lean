import LX.LiftedModel
import LX.PeriodicBuffer
import Mathlib


/-! Counts of rotations and exchanges in literal L/R/X words.
These counts are used by the finite support and service estimates.
Each letter contributes to exactly one of the two counts. -/
namespace LX.Core.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

def rotations (w : List Letter) : ℕ := (w.filter (fun a => a ≠ .x)).length

def exchanges (w : List Letter) : ℕ := (w.filter (fun a => a = .x)).length


end LX.Core.BufferProgram
