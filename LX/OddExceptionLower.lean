import LX.EvenBoundaryBase
import LX.ExceptionalPriceLower
import LX.OddSingleRaise
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_exception_base (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (i : Fin n) :
    oddBase m hm hn (((m+2 : ℕ)) : Fin n) i=oddException m i := by
  have hcv : (((m+2 : ℕ) : Fin n)).val=m+2 := Nat.mod_eq_of_lt (by omega)
  have hci := congrArg (fun k : ℕ => (k : ℤ)) hcv
  have hil := i.isLt
  unfold oddBase perturbedBoard
  change center (n := n) m (((((m+2 : ℕ)) : Fin n) : ℤ)+1-(oddRankValue m i.val : ℤ)-(i : ℤ))=oddException m i
  rw [hci]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  by_cases hi0 : i.val=0
  · norm_num only [oddRankValue,oddException,hi0,Nat.cast_zero]
    simp only [ite_true,ite_false,false_and]
    apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
  · by_cases hi1 : i.val=1
    · norm_num only [oddRankValue,oddException,hi1,Nat.cast_one]
      simp only [ite_true,ite_false,false_and]
      apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
    · by_cases hi2 : i.val=2
      · norm_num only [oddRankValue,oddException,hi2,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
        simp only [ite_true,ite_false,false_and]
        apply center_eq_of_translate m _ _ 0 <;> (try constructor) <;> omega
      · have hi3 : 3 ≤ i.val := by omega
        by_cases hiM : i.val ≤ m+1
        · simp only [oddRankValue,oddException,ite_eq_right hi0,ite_eq_right hi1,
            ite_eq_right hi2,ite_eq_left hiM,ite_eq_left (show 3 ≤ i.val ∧ i.val ≤ m+1 from ⟨hi3,hiM⟩)]
          apply center_eq_of_translate m _ _ 0 <;> (try constructor) <;> omega
        · simp only [oddRankValue,oddException,ite_eq_right hi0,ite_eq_right hi1,
            ite_eq_right hi2,ite_eq_right hiM,
            ite_eq_right (show ¬(3 ≤ i.val ∧ i.val ≤ m+1) by omega)]
          apply center_eq_of_translate m _ _ (-1) <;> (try constructor) <;> omega

theorem odd_exception_balance (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    (∑ i : Fin n,oddException m i)=0 := by
  let f : ℕ → ℤ := fun k => if k=0 then 2-(m : ℤ) else if k=1 then -(m : ℤ)
    else if k=2 then 0 else if k ≤ m+1 then (m : ℤ)+4-2*k else 3*(m : ℤ)+4-2*k
  change (∑ i : Fin n,f i.val)=0
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-1) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,f k)=2-2*(m : ℤ) := by
    norm_num [Finset.sum_range_succ,f]
    ring
  have hmid : (∑ k ∈ Finset.range (m-1),f (3+k))=
      ((m-1 : ℕ) : ℤ)*((m : ℤ)-2)-2*∑ k ∈ Finset.range (m-1),(k : ℤ) := by
    have hp (k : ℕ) (hk : k ∈ Finset.range (m-1)) : f (3+k)=(m : ℤ)-2-2*k := by
      have := Finset.mem_range.mp hk
      dsimp only [f]
      split_ifs <;> push_cast <;> omega
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  have htail : (∑ k ∈ Finset.range (m-1),f (3+(m-1)+k))=
      ((m-1 : ℕ) : ℤ)*(m : ℤ)-2*∑ k ∈ Finset.range (m-1),(k : ℤ) := by
    have hp (k : ℕ) (hk : k ∈ Finset.range (m-1)) : f (3+(m-1)+k)=(m : ℤ)-2*k := by
      dsimp only [f]
      split_ifs <;> push_cast <;> omega
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hfirst,hmid,htail]
  have hs : (∑ j ∈ Finset.range (m-1),(j : ℤ))*2=((m-1 : ℕ) : ℤ)*((m-1-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun t : ℕ => (t : ℤ)) (Finset.sum_range_id_mul_two (m-1))
    convert hh using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hm2 : ((m-1-1 : ℕ) : ℤ)=(m : ℤ)-2 := by omega
  rw [hm1,hm2] at hs
  rw [hm1]
  nlinarith

theorem odd_exception_phase_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : c=((m+2 : ℕ) : Fin n)) {d : Fin n → ℤ}
    (hd : IsLift (odd m hm hn) (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  subst c
  have hbase : oddBase m hm hn (((m+2 : ℕ)) : Fin n)=oddException m :=
    funext (odd_exception_base m hm hn)
  rcases odd_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
  · rw [hbase] at he
    rw [he] at hd hg hu
    have hh := odd_exception_price_lower m hm hn hd hg
    omega
  · have hz := hd.1
    rw [ha,hbase] at hz
    have hs : (∑ i : Fin n,raiseAt (oddException m) a i)=
        (∑ i : Fin n,oddException m i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
    rw [hs,odd_exception_balance m hm hn] at hz
    have := NeZero.pos n
    omega

#print axioms odd_exception_phase_lower
end LX.Antipode
