import LX.OddMiddlePair
import LX.OddOuterMass
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_outer_bad_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : (c.val ≤ 1 ∧ (c.val+m)%2=1) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=0)) :
    (n : ℤ) ≤ ∑ i,oddBase m (by omega) hn c i := by
  have hw := odd_outer_special_wrap m hm hn c (by rcases hc with hc | hc <;> omega)
  have hs := odd_special_wrap_mass m (by omega) hn c hw
  have hS : oddMidTop m c=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have ht := (Finset.mem_filter.mp hj).2
    have he := odd_mid_top_equations m (by omega) hn c j ht.1 ht.2.1 ht.2.2
    rcases hc with hc | hc <;> omega
  simpa only [hS,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero] using hs

theorem odd_outer_lift_unique (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) {d : Fin n → ℤ}
    (hd : IsLift (odd m (by omega) hn) (c : ℤ) d) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=oddBase m (by omega) hn c := by
  rcases odd_lift_single_raise m (by omega) hn c hd hlo with he | ⟨a,ha⟩
  · exact he
  · have hmass := odd_outer_base_nonnegative m hm hn c hc
    have hz := hd.1
    rw [ha] at hz
    have hs : (∑ i : Fin n,raiseAt (oddBase m (by omega) hn c) a i)=
        (∑ i : Fin n,oddBase m (by omega) hn c i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
    rw [hs] at hz
    have := NeZero.pos n
    omega

theorem odd_outer_phase_parity (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) {d : Fin n → ℤ}
    (hd : IsLift (odd m (by omega) hn) (c : ℤ) d) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    (c.val ≤ 1 ∧ (c.val+m)%2=0) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=1) := by
  have he := odd_outer_lift_unique m hm hn c hc hd hlo
  have hz := hd.1
  rw [he] at hz
  rcases hc with hc | hc
  · left
    refine ⟨hc,?_⟩
    by_contra hnot
    have hs := odd_outer_bad_mass m hm hn c (Or.inl ⟨hc,by omega⟩)
    rw [hz] at hs
    have := NeZero.pos n
    omega
  · right
    refine ⟨hc,?_⟩
    by_contra hnot
    have hs := odd_outer_bad_mass m hm hn c (Or.inr ⟨hc,by omega⟩)
    rw [hz] at hs
    have := NeZero.pos n
    omega

theorem odd_outer_minimum_location (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : (c.val ≤ 1 ∧ (c.val+m)%2=0) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=1)) :
    ∃ t : Fin n,m+2 ≤ t.val ∧ oddBase m (by omega) hn c t= -(m : ℤ) := by
  have hclt := c.isLt
  rcases hc with ⟨hc,hpar⟩ | ⟨hc,hpar⟩
  · let k : ℕ := (c.val+3*m+2)/2
    have hk : 2*k=c.val+3*m+2 := by dsimp [k]; omega
    have hklo : m+2 ≤ k := by omega
    have hkhi : k < n := by omega
    let t : Fin n := ⟨k,hkhi⟩
    have hr : (oddRank m (by omega) hn t).val=k := by
      change oddRankValue m k=k
      simp only [oddRankValue,ite_eq_right (by omega : k ≠ 2),
        ite_eq_right (by omega : ¬(3 ≤ k ∧ k ≤ m+1))]
    refine ⟨t,hklo,?_⟩
    unfold oddBase perturbedBoard
    rw [hr]
    change center (n := n) m ((c : ℤ)+1-(k : ℤ)-(k : ℤ))= -(m : ℤ)
    apply center_eq_of_translate m _ _ (-1)
    · omega
    · constructor <;> omega
  · let k : ℕ := (c.val+m+1)/2
    have hk : 2*k=c.val+m+1 := by dsimp [k]; omega
    have hklo : m+2 ≤ k := by omega
    have hkhi : k < n := by omega
    let t : Fin n := ⟨k,hkhi⟩
    have hr : (oddRank m (by omega) hn t).val=k := by
      change oddRankValue m k=k
      simp only [oddRankValue,ite_eq_right (by omega : k ≠ 2),
        ite_eq_right (by omega : ¬(3 ≤ k ∧ k ≤ m+1))]
    refine ⟨t,hklo,?_⟩
    unfold oddBase perturbedBoard
    rw [hr]
    change center (n := n) m ((c : ℤ)+1-(k : ℤ)-(k : ℤ))= -(m : ℤ)
    apply center_eq_of_translate m _ _ 0
    · omega
    · constructor <;> omega

theorem odd_outer_greedy_price_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : c.val ≤ 1 ∨ m+3 ≤ c.val)
    {d : Fin n → ℤ} (hd : IsLift (odd m (by omega) hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  have hlo := odd_unpaid_lower_strip m (by omega) hn hd hg hu
  have he := odd_outer_lift_unique m hm hn c hc hd hlo
  have hpar := odd_outer_phase_parity m hm hn c hc hd hlo
  obtain ⟨t,htlo,htvalue⟩ := odd_outer_minimum_location m hm hn c hpar
  have hdt : d t= -(m : ℤ) := by rw [he]; exact htvalue
  let ρ : State n := oddRank m (by omega) hn
  have hp (i : Fin n) : (odd m (by omega) hn).symm i=1-ρ i := rfl
  have hrt : ρ t=t := by
    apply Fin.ext
    change oddRankValue m t.val=t.val
    simp only [oddRankValue,ite_eq_right (by omega : t.val ≠ 2),
      ite_eq_right (by omega : ¬(3 ≤ t.val ∧ t.val ≤ m+1))]
  have hR := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp t (by omega) (by rw [hrt]; omega)
  rw [hrt,hdt] at hR
  have hI := odd_lift_inversions_lower m (by omega) hn hd
  have hI' : (m : ℤ)^2 ≤ (inversions d : ℤ)+((m-1 : ℕ) : ℤ) := by exact_mod_cast hI
  have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-m+1 : ℕ) : ℤ) := by exact_mod_cast hu
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hu'
  push_cast at hu'
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have ht' : (m : ℤ)+2 ≤ t := by omega
  rw [hn'] at hR
  rw [hm1] at hI'
  nlinarith only [hR,hI',hu',ht']

#print axioms odd_outer_greedy_price_lower
end LX.Antipode
