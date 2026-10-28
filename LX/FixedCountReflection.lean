import LX.MatchingCircularReflection
import Mathlib

namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

def fixedPositions (p : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i=i)

@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]

theorem fixed_positions_card (p : State n) :
    ((fixedPositions p).card : ℤ)=(n : ℤ)-(p.support.card : ℤ) := by
  have hs : fixedPositions p=Finset.univ \ p.support := by
    ext i
    simp [Equiv.Perm.mem_support]
  have hc : p.support.card ≤ n := by simpa using p.support.card_le_univ
  rw [hs,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hc]

theorem fixed_count_one_reflection [NeZero n] (p : State n)
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hcard : (fixedPositions p).card=1)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i, p i= -i := by
  have hfixed : ∀ i, p i=i → i=0 := by
    intro i hi
    exact Finset.card_le_one.mp (by omega : (fixedPositions p).card ≤ 1)
      i ((mem_fixedPositions p i).mpr hi) 0 ((mem_fixedPositions p 0).mpr hzero)
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k => exact sole_fixed_circular_reflection p hinv hnc hzero hfixed hunique

theorem fixed_count_two_reflection [NeZero n] (p : State n)
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hcard : (fixedPositions p).card=2)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i, p i= -i := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hcard
  have hmem : (0 : Fin n) ∈ ({a,b} : Finset (Fin n)) := by
    rw [← hs]
    exact (mem_fixedPositions p 0).mpr hzero
  have hzeroab : (0 : Fin n)=a ∨ (0 : Fin n)=b := by simpa using hmem
  rcases hzeroab with ha | hb
  · subst a
    have hb0 : 0<b.val := by
      have hbne : b.val ≠ 0 := fun h => hab (Fin.ext h).symm
      omega
    apply two_fixed_circular_reflection p hinv hnc b hb0
      (fun i => by rw [← mem_fixedPositions,hs]; simp) hnoadj
  · subst b
    have ha0 : 0<a.val := by
      have hane : a.val ≠ 0 := fun h => hab (Fin.ext h)
      omega
    apply two_fixed_circular_reflection p hinv hnc a ha0
      (fun i => by rw [← mem_fixedPositions,hs]; simp [or_comm]) hnoadj

#print axioms fixed_count_one_reflection
#print axioms fixed_count_two_reflection
end LX.Core.FiniteCuts
