import LX.SmallExchangeReserve

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The quadratic crowding inequality limits the initial maximum-depth
block to 33 positions. Its phase need not be majorized: up to 1019 extra
exchanges are allowed and charged through the actual source energy. -/
theorem even_second_near_minimum_head {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n) (hn : n=2*height p b+4)
    (hpos : 0 < height p b) (K : ℕ)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hK : K ≤ 1019) :
    ∃ r : Fin n,r.val ≤ 33 ∧ backwardDepth (displacement p b) r < height p b := by
  let d := displacement p b
  let h := height p b
  have hd := is_lift p b
  have hm := near_majorized_of_exchange_allowance ha b K hx
  have hmax (i : Fin n) : backwardDepth d i ≤ h := by
    exact_mod_cast (candidate_price_components p b).2 i
  have hwidth (i j : Fin n) : d i-d j ≤ (n : ℤ) :=
    (displacement_strict_width p b i j).le
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have hh := hmax i
    omega
  have hquad := near_depth_count_quadratic hd hm hwidth h
  change (depthCount d h : ℤ)*((depthCount d h : ℤ)-(n : ℤ)+2*h-2*depthCount d (h+1)) ≤ K at hquad
  rw [hz,Nat.cast_zero,mul_zero,sub_zero] at hquad
  have hn' : (n : ℤ)=2*(h : ℤ)+4 := by exact_mod_cast hn
  have hf : depthCount d h ≤ 33 := by
    by_contra hnot
    have hlo : (34 : ℤ) ≤ depthCount d h := by omega
    have hp := mul_nonneg (show (0 : ℤ) ≤ (depthCount d h : ℤ)-34 by omega)
      (show (0 : ℤ) ≤ (depthCount d h : ℤ)+30 by omega)
    have hK' : (K : ℤ) ≤ 1019 := by omega
    nlinarith
  obtain ⟨r,hr,hh⟩ := exists_head_with_count d h hpos
  exact ⟨r,hr.trans hf,hh⟩

/-- At the second even height the universal scalar price is already two
below the target quadratic. The bounded initial rotation therefore fits
the fixed constant 32, without a geometric phase-selection assumption. -/
theorem even_second_near_minimum_upper_word {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a) (b : Fin n)
    (hn : n=2*height p b+4) (K : ℕ)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hK : K ≤ 1019) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases hz : height p b=0
  · obtain ⟨w,hw,hprice⟩ := candidate_word_bound (by omega : 2 ≤ n) p b
    rw [hz] at hprice
    norm_num at hprice
    have hn' : n=4 := by omega
    refine ⟨w,hw,?_⟩
    rw [hn'] at *
    norm_num at *
    omega
  · obtain ⟨r,hr,hhead⟩ := even_second_near_minimum_head ha b hn (by omega) K hx hK
    obtain ⟨w,hw,hprice⟩ := word_with_nonmaximal_head (by omega : 2 ≤ n) p (phase p b)
      (displacement p b) (is_lift p b) (height p b) r
      (fun i => by exact_mod_cast (candidate_price_components p b).2 i) hhead
    have hcap := (candidate_price_components p b).1
    have hn' : (n : ℤ)=2*(height p b : ℤ)+4 := by exact_mod_cast hn
    have hr' : (r.val : ℤ) ≤ 33 := by omega
    exact ⟨w,hw,by nlinarith⟩

/-- In this height branch, the selected strip has capacity two below the
dimension-wide capacity. Hence a total reserve at most 1021 supplies the
near-minimum allowance used above, even if this anchor is not majorized. -/
theorem even_second_bounded_reserve_upper_word {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a) (b : Fin n)
    (hn : n=2*height p b+4)
    (hreserve : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1021) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  let K := inversions (displacement p b)-inversions (displacement p a)
  have hle := global_minimum_exchanges ha b
  have hx : inversions (displacement p b)=inversions (displacement p a)+K := by
    dsimp only [K]
    omega
  have hK : K ≤ 1019 := by
    have hcap := (candidate_price_components p b).1
    have hdiv : n/2=height p b+2 := by omega
    rw [hdiv] at hreserve
    have hx' : (inversions (displacement p b) : ℤ)=(inversions (displacement p a) : ℤ)+K := by
      exact_mod_cast hx
    have hn' : (n : ℤ)=2*(height p b : ℤ)+4 := by exact_mod_cast hn
    push_cast at hreserve
    nlinarith
  exact even_second_near_minimum_upper_word hn4 ha b hn K hx.le hK

/-- Any still-unpaid input admitting this height has reserve at least 1022.
The result applies to the actual minimum-height phase selected earlier. -/
theorem even_second_unpaid_large_reserve {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a) (b : Fin n)
    (hn : n=2*height p b+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    1022 ≤ ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) := by
  by_contra hnot
  exact hunpaid (even_second_bounded_reserve_upper_word hn4 ha b hn (by omega))

/-- All globally minimal phases of an unpaid even input have the maximal
majorized height. Lower global phases are paid by the head construction. -/
theorem even_unpaid_global_height {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) : height p a+1=m := by
  have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
  rw [displacement_anchor] at hh
  by_contra hnot
  have hlow : height p a+2 ≤ m := by omega
  by_cases he : height p a+2=m
  · exact hunpaid (even_second_near_minimum_upper_word hn4 ha a (by omega) 0 (by omega) (by omega))
  · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩

/-- Knowing the actual global height removes the parity loss in the
uniform rotation budget. An unpaid even input has reserve at most n-31. -/
theorem even_unpaid_reserve_upper {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (m : ℤ)*(m-1)-inversions (displacement p a) ≤ (n : ℤ)-31 := by
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  by_contra hnot
  obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
    p (phase p a) (displacement p a) (is_lift p a) (global_minimum_majorized ha)
    (height p a) (by omega) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
  have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
  have hh' : (height p a : ℤ)+1=m := by exact_mod_cast hh
  exact hunpaid ⟨w,hw,by nlinarith⟩

/-- A remaining second-height phase can occur only above size 1052, and
its global minimum still has maximal height and reserve at least 1022. -/
theorem even_second_unpaid_size_lower {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a) (b : Fin n)
    (hn : n=2*height p b+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) : 1054 ≤ n := by
  have hl := even_second_unpaid_large_reserve hn4 ha b hn hunpaid
  have he : n=2*(height p b+2) := by omega
  have hu := even_unpaid_reserve_upper hn4 (height p b+2) he ha hunpaid
  have hdiv : n/2=height p b+2 := by omega
  rw [hdiv] at hl
  push_cast at hl hu
  have hn' : (n : ℤ)=2*(height p b : ℤ)+4 := by exact_mod_cast hn
  have hsize : (1053 : ℤ) ≤ n := by nlinarith
  omega

#print axioms even_second_near_minimum_upper_word
#print axioms even_second_bounded_reserve_upper_word
#print axioms even_second_unpaid_large_reserve
#print axioms even_unpaid_global_height
#print axioms even_unpaid_reserve_upper
#print axioms even_second_unpaid_size_lower
end LX.AnchoredPhases
