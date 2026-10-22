import LX.OddMiddleMass
import LX.AntipodeBoundaryPhase

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem reflection_token_bound (hn : 2 ≤ n) {p : State n} {c : Fin n} {d : Fin n → ℤ}
    (hd : IsLift p (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g)
    (ρ : State n) (hp : ∀ i,p.symm i=1-ρ i) (i : Fin n)
    (hi : 1 ≤ i.val) (hr : 1 ≤ (ρ i).val) :
    (i : ℤ)+(ρ i : ℤ)-(n : ℤ)-1-((n : ℤ)-1)*d i ≤ (paidRotations c g : ℤ) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hq : -p.symm i=ρ i-1 := by rw [hp]; ring
  have hqval : ((ρ i-1 : Fin n).val : ℤ)=(ρ i : ℤ)-1 := by
    rw [Fin.intCast_val_sub_eq_sub_add_ite]
    have hle : (1 : Fin n) ≤ ρ i := by change (1 : Fin n).val ≤ (ρ i).val; omega
    simp only [hle,ite_true,hv1,Nat.cast_one,Nat.cast_zero,add_zero]
  have ht := hg.paid_token_bound hn hd i
  rw [hq,hqval] at ht
  have hip : ((i.val-1 : ℕ) : ℤ)=(i : ℤ)-1 := by omega
  rw [hip] at ht
  unfold targets at ht
  nlinarith

theorem reflection_head_token_bound (hn : 2 ≤ n) {p : State n} {c : Fin n} {d : Fin n → ℤ}
    (hd : IsLift p (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g)
    (hp : p.symm 0=1) :
    ((n : ℤ)-1)*(1-d 0) ≤ (paidRotations c g : ℤ) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h10 : (1 : Fin n) ≠ 0 := by intro hh; have := congrArg Fin.val hh; simp only [hv1,Fin.val_zero] at this; omega
  have hqval : ((-(1 : Fin n)).val : ℤ)=(n : ℤ)-1 := by
    rw [Fin.val_neg,ite_eq_right h10,hv1]
    omega
  have ht := hg.paid_token_bound hn hd 0
  rw [hp,hqval] at ht
  simp only [targets,Fin.val_zero,Nat.cast_zero,Nat.zero_sub,mul_zero,zero_add,zero_sub] at ht
  nlinarith

end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

/-- Two distinct minimal coordinates survive in the low phase interval.
Their explicit positions allow one coordinate to be raised without
losing both token lower bounds. -/
theorem odd_middle_minimum_pair (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    ∃ j t : Fin n,3 ≤ j.val ∧ j.val ≤ m+1 ∧ j ≠ t ∧
      2*j.val+(c.val+m)%2=c.val+m+2 ∧
      ((t=0 ∧ j.val+m=n) ∨ (m+2 ≤ t.val ∧ t.val=j.val+m)) ∧
      oddBase m hm hn c j=((c.val+m)%2 : ℕ)-(m : ℤ) ∧
      oddBase m hm hn c t=((c.val+m)%2 : ℕ)-(m : ℤ) := by
  let k : ℕ := (c.val+m+2)/2
  let ε : ℕ := (c.val+m)%2
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have hk : 2*k+ε=c.val+m+2 := by dsimp [k,ε]; omega
  have hklo : 3 ≤ k := by omega
  have hkhi : k ≤ m+1 := by omega
  let j : Fin n := ⟨k,by omega⟩
  have hrj : (oddRank m hm hn j).val=k-1 := by
    change oddRankValue m k=k-1
    simp only [oddRankValue,ite_eq_right (by omega : k ≠ 2),
      ite_eq_left (show 3 ≤ k ∧ k ≤ m+1 from ⟨hklo,hkhi⟩)]
  have hjvalue : oddBase m hm hn c j=(ε : ℤ)-m := by
    unfold oddBase perturbedBoard
    rw [hrj]
    change center (n := n) m ((c : ℤ)+1-((k-1 : ℕ) : ℤ)-(k : ℤ))=(ε : ℤ)-m
    apply center_eq_of_translate m _ _ 0
    · omega
    · constructor <;> omega
  by_cases ht : k+m < n
  · let t : Fin n := ⟨k+m,ht⟩
    have hrt : (oddRank m hm hn t).val=k+m := by
      change oddRankValue m (k+m)=k+m
      simp only [oddRankValue,ite_eq_right (by omega : k+m ≠ 2),
        ite_eq_right (by omega : ¬(3 ≤ k+m ∧ k+m ≤ m+1))]
    refine ⟨j,t,hklo,hkhi,?_,hk,Or.inr ⟨by change m+2 ≤ k+m; omega,rfl⟩,hjvalue,?_⟩
    · intro he
      have hh := congrArg Fin.val he
      change k=k+m at hh
      omega
    · unfold oddBase perturbedBoard
      rw [hrt]
      change center (n := n) m ((c : ℤ)+1-((k+m : ℕ) : ℤ)-((k+m : ℕ) : ℤ))=(ε : ℤ)-m
      apply center_eq_of_translate m _ _ (-1)
      · push_cast; omega
      · constructor <;> omega
  · have hteq : k+m=n := by omega
    refine ⟨j,0,hklo,hkhi,?_,hk,Or.inl ⟨rfl,hteq⟩,hjvalue,?_⟩
    · intro he
      have hh := congrArg Fin.val he
      change k=0 at hh
      omega
    · have hr0 : (oddRank m hm hn (0 : Fin n)).val=0 := by simp [oddRank,oddRankValue]
      unfold oddBase perturbedBoard
      rw [hr0]
      simp only [Fin.val_zero,Nat.cast_zero,sub_zero]
      apply center_eq_of_translate m _ _ 1
      · omega
      · constructor <;> omega

#print axioms odd_middle_minimum_pair
end LX.Antipode
