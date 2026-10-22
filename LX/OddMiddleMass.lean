import LX.OddRaisedInversions
import LX.EvenBoundaryBase

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_no_mid_top_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hno : ∀ i : Fin n,3 ≤ i.val → i.val ≤ m+1 → reflectionBoard m ((c : ℤ)+1) i ≠ (m : ℤ)) :
    0 ≤ ∑ i,oddBase m hm hn c i := by
  let ρ : State n := oddRank m hm hn
  let e : Fin n → ℤ := reflectionBoard m ((c : ℤ)+1)
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ)) ≤ oddBase m hm hn c i := by
    have hb := center_bounds (n := n) m ((c : ℤ)+1-2*(i : ℤ))
    have hupper : e i+((i : ℤ)-(ρ i : ℤ)) < (n : ℤ)-m := by
      by_cases hi : 3 ≤ i.val ∧ i.val ≤ m+1
      · have hneq := hno i hi.1 hi.2
        have hδ : (i : ℤ)-(ρ i : ℤ)=1 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ)=1
          unfold oddRankValue
          rw [ite_eq_right (by omega : i.val ≠ 2),ite_eq_left hi]
          omega
        change -(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m at hb
        change e i ≠ (m : ℤ) at hneq
        omega
      · have hδ : (i : ℤ)-(ρ i : ℤ) ≤ 0 := by
          change (i : ℤ)-(oddRankValue m i.val : ℤ) ≤ 0
          unfold oddRankValue
          split_ifs <;> omega
        change -(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m at hb
        omega
    have hh := le_center_of_below_top (n := n) m (e i+((i : ℤ)-(ρ i : ℤ))) hupper
    dsimp only [e,reflectionBoard] at hh
    rw [← center_add] at hh
    have he : (c : ℤ)+1-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=(c : ℤ)+1-(ρ i : ℤ)-(i : ℤ) := by ring
    rw [he] at hh
    exact hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have he : (∑ i : Fin n,e i)=0 := odd_reflection_board_sum m hn ((c : ℤ)+1)
  simpa only [Finset.sum_add_distrib,he,hδ,zero_add] using hs

theorem odd_middle_no_top (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) (hpar : (c.val+m)%2=1)
    (j : Fin n) (hj : 3 ≤ j.val) (hjl : j.val ≤ m+1) :
    reflectionBoard m ((c : ℤ)+1) j ≠ (m : ℤ) := by
  intro he
  let z : ℤ := (c : ℤ)+1-2*(j : ℤ)
  change center (n := n) m z=(m : ℤ) at he
  have hzhi : z < (m : ℤ) := by dsimp [z]; omega
  have hzlo : 1-2*(m : ℤ) ≤ z := by dsimp [z]; omega
  by_cases hz : -(m : ℤ) ≤ z
  · have hh := center_eq_of_translate (n := n) m z z 0 (by ring)
      ⟨hz,by omega⟩
    rw [hh] at he
    omega
  · have hh := center_eq_of_translate (n := n) m z (z+n) (-1) (by ring)
      ⟨by omega,by omega⟩
    rw [hh] at he
    dsimp only [z] at he
    omega

theorem odd_middle_raised_parity (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    (c.val+m)%2=0 := by
  by_contra hnot
  have hpar : (c.val+m)%2=1 := by omega
  have hmass := odd_no_mid_top_mass m hm hn c (odd_middle_no_top m hm hn c hc hcl hpar)
  have hs : (∑ i : Fin n,raiseAt (oddBase m hm hn c) a i)=
      (∑ i : Fin n,oddBase m hm hn c i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
  have hz := hd.1
  rw [hs] at hz
  have := NeZero.pos n
  omega

#print axioms odd_middle_raised_parity
end LX.Antipode
