import LX.OddMiddlePair

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every lift in the middle phase interval meets the sharp odd price.
The argument includes both unraised and single-raised profiles. -/
theorem odd_middle_greedy_price_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    {d : Fin n → ℤ} (hd : IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  let ε : ℕ := (c.val+m)%2
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hK : (2 : ℤ)*(((m-c.val+1)/2 : ℕ) : ℤ)=(m : ℤ)-(c : ℤ)+ε := by dsimp [ε]; omega
  let ρ : State n := oddRank m hm hn
  have hp (i : Fin n) : (odd m hm hn).symm i=1-ρ i := rfl
  obtain ⟨j,t,hjlo,hjhi,hjt,hjtwice,htloc,hjbase,htbase⟩ := odd_middle_minimum_pair m hm hn c hc hcl
  change 2*j.val+ε=c.val+m+2 at hjtwice
  change oddBase m hm hn c j=(ε : ℤ)-m at hjbase
  change oddBase m hm hn c t=(ε : ℤ)-m at htbase
  have hjtwice' : 2*(j : ℤ)+ε=(c : ℤ)+m+2 := by exact_mod_cast hjtwice
  have hmid (hdj : d j=(ε : ℤ)-m) :
      2*(m : ℤ)^2+(c : ℤ)-m-1-(n : ℤ)*ε ≤ (paidRotations c g : ℤ) := by
    have hrj : (ρ j).val=j.val-1 := by
      change oddRankValue m j.val=j.val-1
      simp only [oddRankValue,ite_eq_right (by omega : j.val ≠ 2),
        ite_eq_left (show 3 ≤ j.val ∧ j.val ≤ m+1 from ⟨hjlo,hjhi⟩)]
    have ht := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp j (by omega)
      (by rw [hrj]; omega)
    have hrj' : (ρ j : ℤ)=(j : ℤ)-1 := by rw [hrj]; omega
    rw [hrj',hdj] at ht
    rw [hn'] at ht ⊢
    nlinarith only [ht,hjtwice']
  have htail (hdt : d t=(ε : ℤ)-m) :
      2*(m : ℤ)^2+m+(c : ℤ)-(n : ℤ)*ε ≤ (paidRotations c g : ℤ) := by
    rcases htloc with ⟨ht0,hkn⟩ | ⟨htlo,htval⟩
    · subst t
      have hr0 : ρ 0=0 := by apply Fin.ext; simp [ρ,oddRank,oddRankValue]
      have hq0 : (odd m hm hn).symm 0=1 := by rw [hp,hr0,sub_zero]
      have ht := reflection_head_token_bound (by omega : 2 ≤ n) hd hg hq0
      rw [hdt] at ht
      rw [hn'] at ht ⊢
      have hcm : (c : ℤ)=(m : ℤ)+ε := by omega
      rw [hcm]
      nlinarith
    · have hrt : ρ t=t := by
        apply Fin.ext
        change oddRankValue m t.val=t.val
        simp only [oddRankValue,ite_eq_right (by omega : t.val ≠ 2),
          ite_eq_right (by omega : ¬(3 ≤ t.val ∧ t.val ≤ m+1))]
      have ht := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp t (by omega)
        (by rw [hrt]; omega)
      rw [hrt,hdt] at ht
      rw [hn'] at ht ⊢
      have htval' : (t : ℤ)=(j : ℤ)+m := by exact_mod_cast htval
      rw [htval'] at ht
      nlinarith
  have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-m+1 : ℕ) : ℤ) := by exact_mod_cast hu
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hu'
  push_cast at hu'
  rcases odd_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
  · have hI : m*(m-1)+1+2*((m-c.val+1)/2) ≤ inversions d := by
      rw [he]
      exact odd_middle_base_inversions m hm hn c hc hcl
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ)+1+2*(((m-c.val+1)/2 : ℕ) : ℤ) ≤ (inversions d : ℤ) := by
      exact_mod_cast hI
    rw [hm1,hK] at hI'
    have hdt : d t=(ε : ℤ)-m := by rw [he]; exact htbase
    have hR := htail hdt
    rw [hn'] at hR
    have hprod := mul_nonneg (Nat.cast_nonneg m : (0 : ℤ) ≤ m)
      (show (0 : ℤ) ≤ 1-(ε : ℤ) by omega)
    nlinarith only [hI',hR,hu',hprod]
  · have hda : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a) := by rwa [ha] at hd
    have hε0 : ε=0 := odd_middle_raised_parity m hm hn c a hc hcl hda
    have hI : m*(m-1)+1+2*((m-c.val+1)/2)+2 ≤ inversions d := by
      rw [ha]
      exact odd_middle_raised_inversions m hm hn c a hc hcl hda
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ)+1+2*(((m-c.val+1)/2 : ℕ) : ℤ)+2 ≤ (inversions d : ℤ) := by
      exact_mod_cast hI
    rw [hm1,hK,hε0,Nat.cast_zero,add_zero] at hI'
    have hR : 2*(m : ℤ)^2+(c : ℤ)-m-1 ≤ (paidRotations c g : ℤ) := by
      by_cases hat : a=t
      · have hdj : d j=(ε : ℤ)-m := by
          rw [ha]
          simp only [raiseAt,ite_eq_right (show j ≠ a by rw [hat]; exact hjt),Nat.cast_zero,add_zero]
          exact hjbase
        have hh := hmid hdj
        simpa only [hε0,Nat.cast_zero,mul_zero,sub_zero] using hh
      · have hdt : d t=(ε : ℤ)-m := by
          rw [ha]
          simp only [raiseAt,ite_eq_right (Ne.symm hat),Nat.cast_zero,add_zero]
          exact htbase
        have hh := htail hdt
        rw [hε0,Nat.cast_zero,mul_zero,sub_zero] at hh
        nlinarith
    nlinarith only [hI',hR,hu']

#print axioms odd_middle_greedy_price_lower
end LX.Antipode
