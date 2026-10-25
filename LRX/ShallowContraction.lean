import LRX.FiniteCutLoad
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem displacement_mass_inverse (p : State n) :
    (∑ i : Fin n, |displacement p.symm i|)=∑ i : Fin n, |displacement p i| := by
  have h := Equiv.sum_comp p (fun i : Fin n => |displacement p.symm i|)
  simpa only [displacement,Equiv.symm_apply_apply,abs_sub_comm] using h.symm


end LRX.FiniteCuts
