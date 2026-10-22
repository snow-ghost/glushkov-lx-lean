import LX.ConstantHeightEvenPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The lower odd height can pay a larger terminal interval. The first
nonmaximal head is derived from the actual fixed-fiber count. -/
theorem odd_few_fixed_gap_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 0 < height p a)
    (hf : (fixedPositions (permutation p a)).card ≤ (a-p a).val+1)
    (hgap : (a-p a).val ≤ height p a+32) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count (displacement p a) (height p a) hh
  rw [top_depth_count_eq_fixed] at hr
  let T := height p a*(n-1)+(a-p a).val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)=0 := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+((a-p a).val : ℤ) := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
  have hg : ((a-p a).val : ℤ) ≤ (height p a : ℤ)+32 := by exact_mod_cast hgap
  exact ⟨w,hw,by nlinarith⟩

/-- Constant anchor height in odd size needs no multiplicity split: the
triangular rank bound makes a two-fiber terminal interval affordable. -/
theorem odd_constant_anchor_height_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a b,height p a=height p b) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  classical
  by_contra hunpaid
  have hn22 : 22 ≤ n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  obtain ⟨a,_,ha⟩ := odd_unpaid_lower_global_minimum hn4 p m hn hunpaid
  let h := height p a
  have hall' (b : Fin n) : height p b=h := hall b a
  have hn' : n=2*h+3 := by dsimp [h]; omega
  obtain ⟨b,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun b => (fixedPositions (permutation p b)).card) ⟨a,Finset.mem_univ _⟩
  let F := (fixedPositions (permutation p b)).card
  have hF (c : Fin n) : (fixedPositions (permutation p c)).card ≤ F := hmax c (Finset.mem_univ _)
  have htri := minimum_height_fixed_triangle p b (fun c => by rw [hall' b,hall' c])
  rw [hall' b] at htri
  change (F : ℤ)*(F-1) ≤ (n : ℤ)*((n : ℤ)-1-2*h) at htri
  have hnI : (n : ℤ)=2*(h : ℤ)+3 := by exact_mod_cast hn'
  have hFsmall : 2*F < n := by
    by_contra hnot
    have hFbig : (11 : ℤ) ≤ F := by omega
    have hp := mul_nonneg (show 0 ≤ (F : ℤ)-11 by omega) (show 0 ≤ (F : ℤ)+6 by positivity)
    nlinarith
  have hbudget : 2*F ≤ h+32 := by
    have hp := sq_nonneg ((F : ℤ)-5)
    have hFnonneg : (0 : ℤ) ≤ F := by positivity
    have he : 2*(F : ℤ) ≤ (h : ℤ)+32 := by nlinarith
    exact_mod_cast he
  let r : Fin n := -(F : Fin n)
  obtain ⟨c,hc⟩ := constant_height_predecessor p h F hall' hF (by omega) r
  have hFv : (F : Fin n).val=F := by simp [Nat.mod_eq_of_lt (by omega : F < n)]
  have he : c-p c=(F : Fin n)+(r-(p c-c)) := by dsimp only [r]; ring
  have hgap : (c-p c).val=F+(r-(p c-c)).val := by
    rw [he,Fin.val_add,hFv,Nat.mod_eq_of_lt (by omega)]
  apply hunpaid
  apply odd_few_fixed_gap_word p c (by rw [hall']; exact hn') (by rw [hall']; omega)
  · have hf := hF c
    omega
  · rw [hall']
    omega

/-- Constant anchor height is now paid for every n >= 4. -/
theorem constant_anchor_height_upper_word (hn4 : 4 ≤ n) (p : State n)
    (hall : ∀ a b,height p a=height p b) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases he : n=2*(n/2)
  · exact even_constant_anchor_height_upper_word hn4 p (n/2) he hall
  · exact odd_constant_anchor_height_upper_word hn4 p (n/2) (by omega) hall

/-- A necessary geometric feature of every remaining critical input: its
actual anchor heights vary. No abstract higher phase is assumed. -/
theorem unpaid_anchor_height_variation (hn4 : 4 ≤ n) (p : State n)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a b : Fin n,height p a < height p b := by
  by_contra hnone
  have hall (a b : Fin n) : height p a=height p b := by
    have hab : ¬height p a < height p b := fun h => hnone ⟨a,b,h⟩
    have hba : ¬height p b < height p a := fun h => hnone ⟨b,a,h⟩
    omega
  exact hunpaid (constant_anchor_height_upper_word hn4 p hall)

/-- The higher phase belongs to the same original critical input, relative
to the already verified minimum-height critical source. -/
theorem unpaid_critical_higher_anchor (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (ha : CriticalPhase p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,height p a < height p b := by
  obtain ⟨b,c,hbc⟩ := unpaid_anchor_height_variation hn4 p hunpaid
  have hb := unpaid_critical_minimum_height hn4 p a ha hunpaid b
  exact ⟨c,lt_of_le_of_lt hb hbc⟩

#print axioms odd_few_fixed_gap_word
#print axioms odd_constant_anchor_height_upper_word
#print axioms constant_anchor_height_upper_word
#print axioms unpaid_anchor_height_variation
#print axioms unpaid_critical_higher_anchor
end LX.AnchoredPhases
