import LX.MinimumEnergyPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- If every global minimum in odd dimension has maximal height, the
singleton minimum is tight and advances the minimum phase by one offset.
The resulting orbit contains every residue, forcing a complete mapping. -/
theorem odd_maximal_minima_complete (p : State n) (m : ℕ) (hn : n=2*m+1)
    (hheight : ∀ a : Fin n,GlobalMinimum p a → height p a=m) : CompleteMapping p := by
  have hstep (a : Fin n) (ha : GlobalMinimum p a) :
      ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+1 := by
    have hh := hheight a ha
    let S := (Finset.univ : Finset (Fin n)).erase a
    have hcard : S.card=n-1 := by simp [S]
    have hsum : (∑ i ∈ S,displacement p a i)=(m : ℤ) := by
      have hs := Finset.sum_erase_add Finset.univ (displacement p a) (Finset.mem_univ a)
      rw [displacement_balance,displacement_anchor,hh] at hs
      change (∑ i ∈ S,displacement p a i)+ -(m : ℤ)=0 at hs
      omega
    have htight : 2*(∑ i ∈ S,displacement p a i)=(S.card : ℤ)*((n : ℤ)-S.card) := by
      rw [hsum,hcard,Nat.cast_sub (NeZero.pos n)]
      norm_num only [Nat.cast_one]
      have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
      nlinarith
    obtain ⟨b,hb,_,hphase,_⟩ := zero_slack_phase ha S htight
    have hbheight := hheight b hb
    rw [hcard,Nat.cast_sub (NeZero.pos n),Fin.natCast_self,Nat.cast_one] at hphase
    simp only [phase,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hh,hbheight] at hphase
    exact ⟨b,hb,by linear_combination -hphase⟩
  obtain ⟨a,ha⟩ := exists_global_minimum p
  have hiter : ∀ k : ℕ,∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+(k : Fin n) := by
    intro k
    induction k with
    | zero => exact ⟨a,ha,by simp⟩
    | succ k ih =>
      obtain ⟨b,hb,hbr⟩ := ih
      obtain ⟨c,hc,hcr⟩ := hstep b hb
      refine ⟨c,hc,?_⟩
      rw [hcr,hbr,Nat.cast_add,Nat.cast_one]
      ring
  apply Finite.injective_iff_surjective.mpr
  intro r
  obtain ⟨b,_,hbr⟩ := hiter (r-(p a-a)).val
  simp only [Fin.cast_val_eq_self] at hbr
  exact ⟨b,by linear_combination hbr⟩


#print axioms odd_maximal_minima_complete
end LX.AnchoredPhases
