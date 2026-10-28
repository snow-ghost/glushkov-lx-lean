import LX.OddMiddleMass
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem add_period_le_center_of_below_bottom (m : ℕ) (z : ℤ) (hz : z < -(m : ℤ)) :
    z+n ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (0 : ℤ)*n by omega)
  have hm := mul_le_mul_of_nonneg_right (show (z+m)/(n : ℤ) ≤ -1 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

def oddMidTop (m : ℕ) (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => 3 ≤ i.val ∧ i.val ≤ m+1 ∧ reflectionBoard m ((c : ℤ)+1) i=m

theorem odd_mid_top_card (m : ℕ) (hn : n=2*m+1) (c : Fin n) : (oddMidTop m c).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply odd_reflection_board_injective m hn ((c : ℤ)+1)
  exact (Finset.mem_filter.mp hi).2.2.2.trans (Finset.mem_filter.mp hj).2.2.2.symm

/-- The special rank at position 2 supplies one whole positive period.
At most one positive mid-rank change can spend that period. -/
theorem odd_special_wrap_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hw : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2) :
    (n : ℤ)-(n : ℤ)*(oddMidTop m c).card ≤ ∑ i,oddBase m hm hn c i := by
  let ρ : State n := oddRank m hm hn
  let e : Fin n → ℤ := reflectionBoard m ((c : ℤ)+1)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have htranslate (i : Fin n) : center (n := n) m (e i+((i : ℤ)-(ρ i : ℤ)))=oddBase m hm hn c i := by
    dsimp only [e,reflectionBoard]
    rw [← center_add]
    unfold oddBase perturbedBoard
    congr 1
    change (c : ℤ)+1-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=(c : ℤ)+1-(ρ i : ℤ)-(i : ℤ)
    ring
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))+
      (if i=2 then (n : ℤ) else 0)-(if i ∈ oddMidTop m c then (n : ℤ) else 0) ≤ oddBase m hm hn c i := by
    rw [← htranslate]
    have hb : -(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m := center_bounds m _
    by_cases hi2 : i=2
    · subst i
      have hδ : ((2 : Fin n) : ℤ)-(ρ 2 : ℤ)=1-(m : ℤ) := by
        change ((2 : Fin n).val : ℤ)-(oddRankValue m (2 : Fin n).val : ℤ)=1-(m : ℤ)
        rw [hv2]
        simp only [oddRankValue,ite_true,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
      have hnot : (2 : Fin n) ∉ oddMidTop m c := by
        intro hh
        have ht : 3 ≤ (2 : Fin n).val := (Finset.mem_filter.mp hh).2.1
        rw [hv2] at ht
        omega
      rw [ite_eq_left (show (2 : Fin n)=2 from rfl),ite_eq_right hnot,sub_zero]
      apply add_period_le_center_of_below_bottom
      change e 2 ≤ -2 at hw
      omega
    · rw [ite_eq_right hi2,add_zero]
      by_cases hmid : 3 ≤ i.val ∧ i.val ≤ m+1
      · have hδ : (i : ℤ)-(ρ i : ℤ)=1 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ)=1
          simp only [oddRankValue,ite_eq_right (by omega : i.val ≠ 2),ite_eq_left hmid]
          omega
        by_cases htop : e i=(m : ℤ)
        · have hmem : i ∈ oddMidTop m c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmid.1,hmid.2,htop⟩
          rw [ite_eq_left hmem]
          exact sub_period_le_center_of_at_top m _ (by omega)
        · have hnot : i ∉ oddMidTop m c := by
            intro hh
            exact htop (Finset.mem_filter.mp hh).2.2.2
          rw [ite_eq_right hnot,sub_zero]
          exact le_center_of_below_top m _ (by omega)
      · have hδ : (i : ℤ)-(ρ i : ℤ)=0 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ)=0
          have hine : i.val ≠ 2 := by intro hh; apply hi2; apply Fin.ext; omega
          simp only [oddRankValue,ite_eq_right hine,ite_eq_right hmid,sub_self]
        have hnot : i ∉ oddMidTop m c := by
          intro hh
          have ht := (Finset.mem_filter.mp hh).2
          exact hmid ⟨ht.1,ht.2.1⟩
        rw [ite_eq_right hnot,sub_zero]
        exact le_center_of_below_top m _ (by omega)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have he : (∑ i : Fin n,e i)=0 := odd_reflection_board_sum m hn ((c : ℤ)+1)
  have hloss : (∑ i : Fin n,if i ∈ oddMidTop m c then (n : ℤ) else 0)=(n : ℤ)*(oddMidTop m c).card := by
    simp [mul_comm]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,he,hδ,hloss,zero_add,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hs

theorem odd_special_wrap_mass_nonnegative (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hw : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2) :
    0 ≤ ∑ i,oddBase m hm hn c i := by
  have hs := odd_special_wrap_mass m hm hn c hw
  have hc := odd_mid_top_card m hn c
  have hc' : ((oddMidTop m c).card : ℤ) ≤ 1 := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left hc' (show (0 : ℤ) ≤ n by positivity)
  nlinarith

theorem odd_mid_top_equations (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c j : Fin n)
    (hj : 3 ≤ j.val) (hjl : j.val ≤ m+1)
    (ht : reflectionBoard m ((c : ℤ)+1) j=(m : ℤ)) :
    2*j.val+m=c.val+1 ∨ 2*j.val=c.val+m+2 := by
  let z : ℤ := (c : ℤ)+1-2*(j : ℤ)
  change center (n := n) m z=(m : ℤ) at ht
  have hclt := c.isLt
  have hzlo : -(n : ℤ) ≤ z := by dsimp [z]; omega
  have hzhi : z < (n : ℤ) := by dsimp [z]; omega
  by_cases hlo : -(m : ℤ) ≤ z
  · by_cases hhi : z ≤ (m : ℤ)
    · have he := center_eq_of_translate (n := n) m z z 0 (by ring) ⟨hlo,by omega⟩
      rw [he] at ht
      left
      dsimp only [z] at ht
      omega
    · have he := center_eq_of_translate (n := n) m z (z-n) 1 (by ring) ⟨by omega,by omega⟩
      rw [he] at ht
      omega
  · have he := center_eq_of_translate (n := n) m z (z+n) (-1) (by ring) ⟨by omega,by omega⟩
    rw [he] at ht
    right
    dsimp only [z] at ht
    omega

theorem odd_outer_special_wrap (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+4 ≤ c.val) : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2 := by
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have he : (c : ℤ)+1-2*((2 : Fin n) : ℤ)=(c : ℤ)-3 := by rw [hv2]; ring
  unfold reflectionBoard
  rw [he]
  rcases hc with hc | hc
  · have hh := center_eq_of_translate (n := n) m ((c : ℤ)-3) ((c : ℤ)-3) 0 (by ring)
      ⟨by omega,by omega⟩
    rw [hh]
    omega
  · have hclt := c.isLt
    have hh := center_eq_of_translate (n := n) m ((c : ℤ)-3) ((c : ℤ)-3-n) 1 (by ring)
      ⟨by omega,by omega⟩
    rw [hh]
    omega

theorem odd_outer_base_nonnegative (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) : 0 ≤ ∑ i,oddBase m (by omega) hn c i := by
  by_cases he : c.val=m+3
  · apply odd_no_mid_top_mass
    intro j hj hjl ht
    have hh := odd_mid_top_equations m (by omega) hn c j hj hjl ht
    omega
  · exact odd_special_wrap_mass_nonnegative m (by omega) hn c
      (odd_outer_special_wrap m hm hn c (by omega))

#print axioms odd_outer_base_nonnegative
end LX.Antipode
