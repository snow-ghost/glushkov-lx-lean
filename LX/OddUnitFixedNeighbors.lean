import LRX.MajorizedExtremeCount
import LX.AnchorPhasePrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem cyclic_offset_normalized (p : State n) (a i : Fin n) :
    cyclicOffset p a i=permutation p a i-i := by
  unfold cyclicOffset
  change p i-i-(p a-a)=p i+(a-p a)-i
  abel

/-- The reverse displacement of a cyclic k-step pair, including a pair
crossing the chosen linear cut. -/
theorem cyclic_pair_reverse_coordinate (p : State n) (a i : Fin n) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) (hpair : permutation p a (permutation p a i)=i)
    (hi : permutation p a i=i+(k : Fin n)) :
    displacement p a (permutation p a i)=(n : ℤ)-k-height p a := by
  have he : cyclicOffset p a (permutation p a i)= -(k : Fin n) := by
    rw [cyclic_offset_normalized,hpair,hi]
    abel
  have hv : (k : Fin n).val=k := by simp [Nat.mod_eq_of_lt hkn]
  have hne : (k : Fin n) ≠ 0 := by
    intro hh
    have hh' := congrArg Fin.val hh
    rw [hv,Fin.val_zero] at hh'
    omega
  have hvneg : (-(k : Fin n)).val=n-k := by simp [Fin.val_neg,hne,hv]
  rw [displacement_offset,he]
  change (((-(k : Fin n)).val : ℕ) : ℤ)-(height p a : ℤ)=_
  rw [hvneg]
  omega

theorem three_fixed_matching_no_cyclic_adjacent (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (hn : n=2*height p a+3)
    (hinv : Function.Involutive (permutation p a)) :
    ∀ i : Fin n,permutation p a i ≠ i+1 := by
  intro i hi
  have hr := cyclic_pair_reverse_coordinate p a i 1 (by omega) (by omega) (hinv i) hi
  have hu := (short_coordinates (is_lift p a).1 hm (permutation p a i)).1
  rw [hr] at hu
  omega

theorem three_fixed_matching_unique_cyclic_gap_two (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (hn : n=2*height p a+3)
    (hinv : Function.Involutive (permutation p a)) :
    ∀ i j : Fin n,permutation p a i=i+2 → permutation p a j=j+2 → i=j := by
  intro i j hi hj
  have hri := cyclic_pair_reverse_coordinate p a i 2 (by omega) (by omega) (hinv i) hi
  have hrj := cyclic_pair_reverse_coordinate p a j 2 (by omega) (by omega) (hinv j) hj
  have hc := majorized_level_count hm ((height p a : ℤ)+1) (by omega)
  have hc1 : (Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1)).card ≤ 1 := by omega
  have him : permutation p a i ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hjm : permutation p a j ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  exact (permutation p a).injective (Finset.card_le_one.mp hc1 _ him _ hjm)


#print axioms cyclic_pair_reverse_coordinate
#print axioms three_fixed_matching_unique_cyclic_gap_two
end LX.AnchoredPhases
