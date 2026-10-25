import LRX.BufferEndpoints
import LRX.FullCycleService
import LRX.ProgramFootprint
import LRX.VisitedPorts
import Mathlib

/-! A finite service certificate records actual commands, exact delivered
coordinates, rotation price, and every port visited by serviced arrows. It is
intended to be enlarged by insertion until all reachable cycles are covered. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

structure ServiceCertificate (p : State n) (d : Fin n → ℤ) where
  labels : Finset (Fin n)
  program : List (Command n)
  invariant : labels.image p.symm=labels
  root_mem : (0 : Fin n) ∈ labels
  uses : ProgramUses labels program
  valid : Valid program initialLogical
  coordinates : ∀ i, (logicalRun program initialLogical).coord i=
    (initialLogical (n := n)).coord i+if i ∈ labels then logicalDelta d i else 0
  final_buffer : p.symm (logicalRun program initialLogical).buffer=0
  rotation_price : rotations (compile program)=∑ i ∈ labels, (logicalDelta d i).natAbs
  ports : ∀ i ∈ labels, ∀ v : ℤ,
    min (i : ℤ) ((i : ℤ)+d i) ≤ v ∧ v ≤ max (i : ℤ) ((i : ℤ)+d i) →
    Visits program initialLogical (PeriodicBuffer.contract (n : ℤ) v)


end LRX.BufferProgram
