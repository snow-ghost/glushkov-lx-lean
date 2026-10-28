import LX.AnchoredPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Select the last occurrence of an arbitrary anchored source, without
assuming that this phase is globally minimal. -/
theorem last_offset_source (p : State n) (a : Fin n) :
    ∃ b : Fin n,p b-b=p a-a ∧ height p b=height p a ∧
      displacement p b=displacement p a ∧
      ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val := by
  classical
  let F := Finset.univ.filter fun i => p i-i=p a-a
  have hF : F.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  let b := F.max' hF
  have hb : p b-b=p a-a := (Finset.mem_filter.mp (Finset.max'_mem F hF)).2
  have hp : permutation p b=permutation p a := by
    apply Equiv.ext
    intro i
    change p i+(b-p b)=p i+(a-p a)
    linear_combination -hb
  have hh : height p b=height p a := by simp only [height,hp]
  refine ⟨b,hb,hh,?_,?_⟩
  · funext i
    simp only [displacement,hp,hh]
  · intro i hi
    exact Finset.le_max' F i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.trans hb⟩)


end LX.AnchoredPhases
