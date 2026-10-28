import LX.ColoredReflectionLower
import LX.OddSingleRaise
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def winding (h : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) : ℤ :=
  -((C-(ρ i : ℤ)-(i : ℤ)+h)/(n : ℤ))

theorem perturbed_board_winding (h : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) :
    LX.AffineScan.targets (perturbedBoard h C ρ) i=C-(ρ i : ℤ)+(n : ℤ)*winding h C ρ i := by
  have he := Int.ediv_mul_add_emod (C-(ρ i : ℤ)-(i : ℤ)+h) (n : ℤ)
  unfold LX.AffineScan.targets perturbedBoard center winding
  nlinarith

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

def oddBaseWinding (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n) : Fin n → ℤ :=
  winding m ((c : ℤ)+1) (oddRank m hm hn)

theorem odd_middle_winding_two (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) : oddBaseWinding m hm hn c 2=0 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hr2 : (oddRank m hm hn (2 : Fin n)).val=m+1 := by
    change oddRankValue m (2 : Fin n).val=m+1
    rw [hv2]
    simp [oddRankValue]
  unfold oddBaseWinding winding
  rw [hr2,hv2]
  have hq : ((c : ℤ)+1-((m+1 : ℕ) : ℤ)-(2 : ℕ)+m)/(n : ℤ)=0 := by
    have hclt := c.isLt
    apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn' <;> push_cast <;> omega
  rw [hq,neg_zero]

theorem odd_middle_tail_winding (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c j : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hj : (c.val+m+2)/2 < j.val) (hjl : j.val ≤ m+1) :
    oddBaseWinding m hm hn c j=1 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hj3 : 3 ≤ j.val := by omega
  have hrj : (oddRank m hm hn j).val=j.val-1 := by
    change oddRankValue m j.val=j.val-1
    simp only [oddRankValue,ite_eq_right (by omega : j.val ≠ 2),
      ite_eq_left (show 3 ≤ j.val ∧ j.val ≤ m+1 from ⟨hj3,hjl⟩)]
  unfold oddBaseWinding winding
  rw [hrj]
  have hq : ((c : ℤ)+1-((j.val-1 : ℕ) : ℤ)-(j : ℤ)+m)/(n : ℤ)= -1 := by
    have hjpred : ((j.val-1 : ℕ) : ℤ)=(j : ℤ)-1 := by omega
    rw [hjpred]
    apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn' <;> omega
  rw [hq]
  norm_num

/-- The opposite-parity rank pairs in the low phase interval provide
the exact extra lower cost needed beyond the uniform reflection bound. -/
theorem odd_middle_opposite_count (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    (m-c.val+1)/2 ≤ (Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧
      decide (oddBaseWinding m hm hn c 2 % 2=0) ≠
        decide (oddBaseWinding m hm hn c j % 2=0)).card := by
  let a : Fin n := ⟨(c.val+m+2)/2,by omega⟩
  let b : Fin n := ⟨m+1,by omega⟩
  have hsub : Finset.Ioc a b ⊆ (Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧
      decide (oddBaseWinding m hm hn c 2 % 2=0) ≠
        decide (oddBaseWinding m hm hn c j % 2=0)) := by
    intro j hj
    have ht := Finset.mem_Ioc.mp hj
    have hja : (c.val+m+2)/2 < j.val := ht.1
    have hjb : j.val ≤ m+1 := ht.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,by omega,hjb,?_⟩
    rw [odd_middle_winding_two m hm hn c hc,odd_middle_tail_winding m hm hn c j hc hcl hja hjb]
    decide
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Ioc] at hcard
  have hlen : b.val-a.val=(m-c.val+1)/2 := by dsimp only [a,b]; omega
  rwa [hlen] at hcard

theorem odd_middle_base_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    m*(m-1)+1+2*((m-c.val+1)/2) ≤ inversions (oddBase m hm hn c) := by
  have hF (i : Fin n) : targets (oddBase m hm hn c) i=
      ((c : ℤ)+1)-(oddRank m hm hn i : ℤ)+(n : ℤ)*oddBaseWinding m hm hn c i :=
    perturbed_board_winding m ((c : ℤ)+1) (oddRank m hm hn) i
  have hI := odd_colored_inversions_lower m hm hn (oddBase m hm hn c) ((c : ℤ)+1)
    (oddBaseWinding m hm hn c) hF
  have hK := odd_middle_opposite_count m hm hn c hc hcl
  have hm1 : m-1+1=m := by omega
  nlinarith

#print axioms odd_middle_base_inversions
end LX.Antipode
