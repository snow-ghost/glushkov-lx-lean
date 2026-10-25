import LX.EvenSingleRaise
import LX.ExceptionalPrefixDelay
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem center_eq_of_translate (m : ℕ) (z v k : ℤ)
    (hz : z=v+(n : ℤ)*k) (hv : -(m : ℤ) ≤ v ∧ v < (n : ℤ)-m) :
    center (n := n) m z=v := by
  have he : z+m=(v+m)+k*(n : ℤ) := by rw [hz]; ring
  unfold center
  rw [he,Int.add_emod]
  simp only [Int.mul_emod_left,add_zero,Int.emod_eq_of_lt (by omega : 0 ≤ v+m)
    (by omega : v+m < (n : ℤ))]
  omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

/-- The base at the boundary phase is the already analyzed exceptional
lift, uniformly shifted down by one. -/
theorem even_boundary_base (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (i : Fin n) :
    evenBase m (((m+2 : ℕ)) : Fin n) i=evenException m i-1 := by
  have hcv : (((m+2 : ℕ) : Fin n)).val=m+2 := Nat.mod_eq_of_lt (by omega)
  have hci := congrArg (fun k : ℕ => (k : ℤ)) hcv
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hn' : (n : ℤ)=2*m := by omega
  have hil := i.isLt
  unfold evenBase perturbedBoard
  rw [hci]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  by_cases hi0 : i.val=0
  · have hi1 : i ≠ 1 := by intro he; have := congrArg Fin.val he; omega
    have hi2 : i ≠ 2 := by intro he; have := congrArg Fin.val he; omega
    rw [Equiv.swap_apply_of_ne_of_ne hi1 hi2]
    simp only [evenException,hi0,ite_true,Nat.cast_zero]
    apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
  · by_cases hi2 : i.val ≤ 2
    · have hsum : (i : ℤ)+((Equiv.swap (1 : Fin n) 2) i : ℤ)=3 := by
        have hc : i=1 ∨ i=2 := by
          by_cases he : i.val=1
          · exact Or.inl (Fin.ext (by omega))
          · exact Or.inr (Fin.ext (by omega))
        rcases hc with rfl | rfl <;>
          simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,hv1,hv2,Nat.cast_ofNat] <;> norm_num
      simp only [evenException,ite_eq_right hi0,ite_eq_left hi2]
      apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
    · have hi1' : i ≠ 1 := by intro he; have := congrArg Fin.val he; omega
      have hi2' : i ≠ 2 := by intro he; have := congrArg Fin.val he; omega
      rw [Equiv.swap_apply_of_ne_of_ne hi1' hi2']
      simp only [evenException,ite_eq_right hi0,ite_eq_right hi2]
      by_cases hiM : i.val ≤ m+1
      · rw [ite_eq_left hiM]
        apply center_eq_of_translate m _ _ 0 <;> (try constructor) <;> omega
      · rw [ite_eq_right hiM]
        apply center_eq_of_translate m _ _ (-1) <;> (try constructor) <;> omega

theorem even_exception_balance (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (∑ i : Fin n,evenException m i)=0 := by
  let f : ℕ → ℤ := fun k => if k=0 then 4-(m : ℤ) else if k ≤ 2 then 1-(m : ℤ)
    else if k ≤ m+1 then (m : ℤ)+4-2*k else 3*(m : ℤ)+4-2*k
  change (∑ i : Fin n,f i.val)=0
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-2) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,f k)=6-3*(m : ℤ) := by
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
  have htail : (∑ k ∈ Finset.range (m-2),f (3+(m-1)+k))=
      ((m-2 : ℕ) : ℤ)*(m : ℤ)-2*∑ k ∈ Finset.range (m-2),(k : ℤ) := by
    have hp (k : ℕ) (hk : k ∈ Finset.range (m-2)) : f (3+(m-1)+k)=(m : ℤ)-2*k := by
      dsimp only [f]
      split_ifs <;> push_cast <;> omega
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hfirst,hmid,htail]
  have hsum (k : ℕ) : (∑ j ∈ Finset.range k,(j : ℤ))*2=(k : ℤ)*((k-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun t : ℕ => (t : ℤ)) (Finset.sum_range_id_mul_two k)
    convert hh using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have h1 := hsum (m-1)
  have h2 := hsum (m-2)
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hm2 : ((m-2 : ℕ) : ℤ)=(m : ℤ)-2 := by omega
  have hm11 : ((m-1-1 : ℕ) : ℤ)=(m : ℤ)-2 := by omega
  have hm21 : ((m-2-1 : ℕ) : ℤ)=(m : ℤ)-3 := by omega
  rw [hm1,hm11] at h1
  rw [hm2,hm21] at h2
  rw [hm1,hm2]
  nlinarith

theorem even_boundary_base_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (∑ i : Fin n,evenBase m (((m+2 : ℕ)) : Fin n) i)= -(n : ℤ) := by
  simp only [even_boundary_base m hm hn,Finset.sum_sub_distrib,even_exception_balance m hm hn]
  simp

#print axioms even_boundary_base
#print axioms even_boundary_base_mass
end LX.Antipode
