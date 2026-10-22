import LX.EvenTerminalTwo

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A nonzero head makes the singleton terminal phase shallow enough at
the initial cursor to pay its literal finish of two rotations. -/
theorem even_unpaid_head_fixed (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : p 0=0 := by
  by_contra hp0
  have hhead := even_unpaid_head_minimum p a hn hh hmin hunpaid
  have hv0 : 0 < (p 0).val := Fin.pos_iff_ne_zero.mpr hp0
  have hneg : (-p 0).val=n-(p 0).val := by simp [Fin.val_neg,hp0]
  have hgap0 : (0-p 0).val=(-p 0).val := by simp
  have hpbound : (p 0).val+2 < n := by
    have hp := (p 0).isLt
    by_contra hnot
    exact even_unpaid_small_gap_not_minimum p a 0 hn hh hmin hunpaid
      (by rw [hgap0,hneg]; omega) (by rw [hgap0,hneg]; omega) hhead
  obtain ⟨b,hheight,hraw,hf,_,hfinish,hlast⟩ := even_unpaid_terminal_two p a hn hh hmin hunpaid
  have hbhead : p 0 ≠ p b-b := by
    intro he
    have heh := equal_raw_offset_height p 0 b (by simpa using he)
    omega
  have hv2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (show 2<n by omega)]
  have hoff : cyclicOffset p b 0=p 0+2 := by
    unfold cyclicOffset
    simp only [sub_zero]
    rw [hraw]
    ring
  have hoffval : (cyclicOffset p b 0).val=(p 0).val+2 := by
    rw [hoff,Fin.val_add,hv2,Nat.mod_eq_of_lt hpbound]
  have hlow : backwardDepth (displacement p b) 0 < height p b-1 := by
    by_contra hnot
    have hw := displacement_depth_width_bound (is_lift p b)
      (fun i j => (displacement_strict_width p b i j).le)
      (height p b-1) 0 (by omega)
    rw [show height p b-1+1=height p b by omega,displacement_offset,
      top_depth_count_eq_fixed,hf] at hw
    change ((cyclicOffset p b 0).val : ℤ)-(height p b : ℤ)+
      (backwardDepth (displacement p b) 0 : ℤ) ≤ 1 at hw
    rw [hoffval] at hw
    omega
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p b (by omega) (by omega)
    hbhead hlast 0 hlow (by simp)
  have hcap := (candidate_price_components p b).1
  have hn' : (n : ℤ)=2*(height p b : ℤ) := by omega
  have hfin : (b.val : ℤ)+((-p b).val : ℤ)=2 := by exact_mod_cast hfinish
  apply hunpaid
  refine ⟨w,hw,?_⟩
  nlinarith only [hprice,hcap,hn',hfin]

/-- Every hypothetical even counterexample would begin with the exact
values `0,-1`. The mirrored inverse will contradict this pattern. -/
theorem even_unpaid_head_pattern (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : p 0=0 ∧ p 1= -1 := by
  have hp0 := even_unpaid_head_fixed p a hn hh hmin hunpaid
  obtain ⟨b,hheight,hraw,_,hor,_,_⟩ := even_unpaid_terminal_two p a hn hh hmin hunpaid
  have hhead := even_unpaid_head_minimum p a hn hh hmin hunpaid
  have hb0 : b ≠ 0 := by intro he; rw [he] at hheight; omega
  have hforward : b.val < (p b).val := by
    rcases hor with hf | hz
    · exact hf
    · exact False.elim (hb0 (p.injective (hz.trans hp0.symm)))
  have hv2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (show 2<n by omega)]
  have hgap : (b-p b).val=2 := by
    have he : b-p b=(2 : Fin n) := by linear_combination -hraw
    rw [he,hv2]
  rw [Fin.coe_sub_iff_lt.mpr (show b < p b from hforward)] at hgap
  have hbpos : 0 < b.val := Fin.pos_iff_ne_zero.mpr hb0
  have hp := (p b).isLt
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hb1 : b=1 := Fin.ext (by omega)
  refine ⟨hp0,?_⟩
  rw [hb1] at hraw
  linear_combination hraw

theorem even_global_unpaid_head_pattern (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : p 0=0 ∧ p 1= -1 := by
  have hbase : 3*(n : ℤ)^2-8*n+12=4*(3*(m : ℤ)^2-4*m+3) := by
    have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
    rw [hn']; ring
  have hstrict : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(0 : ℤ)) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  obtain ⟨a,_,_,hnlarge,_,hh,hmin,_⟩ :=
    conjecture_unpaid_reserve_geometry hn4 p m 0 (by omega) (by omega) hstrict
  exact even_unpaid_head_pattern p a (by omega) (by omega) hmin hunpaid

#print axioms even_unpaid_head_fixed
#print axioms even_unpaid_head_pattern
#print axioms even_global_unpaid_head_pattern
end LX.AnchoredPhases
