import LX.CriticalPhaseReduction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Select the last occurrence of an arbitrary anchored source, without
assuming that this phase is globally minimal. -/
theorem last_offset_source (p : State n) (a : Fin n) :
    ∃ b : Fin n,p b-b=p a-a ∧ height p b=height p a ∧
      displacement p b=displacement p a ∧
      ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val := by
  classical
  let F := Finset.univ.filter fun i => p i-i=p a-a
  have hF : F.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  let b := F.max' hF
  have hb : p b-b=p a-a := (Finset.mem_filter.mp (Finset.max'_mem F hF)).2
  have hp : permutation p b=permutation p a := by
    apply Equiv.ext
    intro i
    change p i+(b-p b)=p i+(a-p a)
    linear_combination -hb
  have hh : height p b=height p a := by simp only [height,hp]
  refine ⟨b,hb,hh,?_,?_⟩
  · funext i
    simp only [displacement,hp,hh]
  · intro i hi
    exact Finset.le_max' F i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.trans hb⟩)

/-- The first critical successor has at most three maximum-depth positions
and eleven positions at the next depth, uniformly in n. -/
theorem near_two_depth_counts {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n)
    (hh : 0 < height p b) (hlo : 2*height p b ≤ n) (hhi : n ≤ 2*height p b+3)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+2) :
    depthCount (displacement p b) (height p b) ≤ 3 ∧
      depthCount (displacement p b) (height p b-1) ≤ 11 := by
  let d := displacement p b
  let h := height p b
  have hd := is_lift p b
  have hm := near_majorized_of_exchange_allowance ha b 2 hx
  have hwidth (i j : Fin n) : d i-d j ≤ (n : ℤ) :=
    (displacement_strict_width p b i j).le
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have hi := (candidate_price_components p b).2 i
    change (backwardDepth d i : ℤ) ≤ (h : ℤ) at hi
    omega
  have ht := near_depth_count_quadratic hd hm hwidth h
  rw [hz,Nat.cast_zero,mul_zero,sub_zero] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have hnhi : (n : ℤ) ≤ 2*(h : ℤ)+3 := by exact_mod_cast hhi
  have hf : depthCount d h ≤ 3 := by
    by_contra hnot
    have hprod := mul_nonneg (show 0 ≤ (depthCount d h : ℤ) by positivity)
      (show 0 ≤ 2*(h : ℤ)+3-n by omega)
    have hp := mul_nonneg (show 0 ≤ (depthCount d h : ℤ)-4 by omega)
      (show 0 ≤ (depthCount d h : ℤ)+1 by positivity)
    nlinarith
  have hg := near_depth_count_quadratic hd hm hwidth (h-1)
  rw [show h-1+1=h by dsimp [h]; omega,
    Nat.cast_sub (by dsimp [h]; omega : 1 ≤ h),Nat.cast_one] at hg
  norm_num only [Nat.cast_ofNat] at hg
  refine ⟨hf,?_⟩
  change depthCount d (h-1) ≤ 11
  by_contra hnot
  have hprod := mul_nonneg (show 0 ≤ (depthCount d (h-1) : ℤ) by positivity)
    (show 0 ≤ 2*(h : ℤ)+3-n by omega)
  have hprod' := mul_nonneg (show 0 ≤ (depthCount d (h-1) : ℤ) by positivity)
    (show 0 ≤ (3 : ℤ)-depthCount d h by omega)
  have hp := mul_nonneg (show 0 ≤ (depthCount d (h-1) : ℤ)-12 by omega)
    (show 0 ≤ (depthCount d (h-1) : ℤ)+1 by positivity)
  nlinarith

/-- A small terminal corner is paid at either lower critical height,
even when there is more than one fixed position. -/
theorem lower_last_corner_upper_word (p : State n) (a : Fin n) (hn22 : 22 ≤ n)
    (hn : n=2*height p a+2 ∨ n=2*height p a+3)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcorner : a.val+(-p a).val < 11) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  let r : Fin n := ⟨a.val+1,by omega⟩
  have hhead : backwardDepth (displacement p a) r < height p a := by
    have hh := (candidate_price_components p a).2 r
    have hne : backwardDepth (displacement p a) r ≠ height p a := by
      intro he
      have hfix := (depth_eq_height_iff_fixed p a r).mp he
      have hoff : p r-r=p a-a := by
        change p r+(a-p a)=r at hfix
        linear_combination hfix
      have hr := hlast r hoff
      dsimp [r] at hr
      omega
    omega
  let T := height p a*(n-1)+a.val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T,r]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)= -p a := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+a.val := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ)+((-p a).val : ℤ) := by
    exact_mod_cast hlen
  have hcap := (candidate_price_components p a).1
  have hc : (a.val : ℤ)+((-p a).val : ℤ) ≤ 10 := by omega
  refine ⟨w,hw,?_⟩
  rcases hn with hn | hn
  · have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
    nlinarith
  · have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
    nlinarith

/-- With at most two fixed positions, a small positive cyclic gap absorbs
the initial rotations in the lower odd branch. -/
theorem odd_two_fixed_small_gap_upper_word (p : State n) (a : Fin n)
    (hn4 : 4 ≤ n) (hn : n=2*height p a+3)
    (hf : (fixedPositions (permutation p a)).card ≤ 2)
    (hglo : 1 ≤ (a-p a).val) (hghi : (a-p a).val ≤ 11) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count (displacement p a) (height p a) (by omega)
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
  exact ⟨w,hw,by nlinarith⟩

#print axioms near_two_depth_counts
#print axioms lower_last_corner_upper_word
#print axioms odd_two_fixed_small_gap_upper_word

/-- Remove the head and corner scheduling obstructions automatically. For
every unpaid critical input this constructs a literal word, using either
the original phase or its first successor, with an exact scalar price.
The terminal-position contribution is retained explicitly; this construction
does not prove that the resulting price satisfies the target bound. -/
theorem unpaid_critical_priced_word (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (ha : CriticalPhase p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ c : Fin n,∃ j : ℕ,j ≤ 2 ∧
      (height p c=height p a ∨ height p c=height p a+1) ∧
      inversions (displacement p c)=inversions (displacement p a)+j ∧
      11 ≤ c.val+(-p c).val ∧ p 0 ≠ p c-c ∧
      (∀ i : Fin n,p i-i=p c-c → i.val ≤ c.val) ∧
      ∃ w : List Letter,p*eval w=1 ∧
        (w.length : ℤ)=(inversions (displacement p a) : ℤ)+j+
          ((height p c : ℤ)-1)*((n : ℤ)-1)+
            (c.val : ℤ)+((-p c).val : ℤ)-1 := by
  have hn22 : 22 ≤ n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  have hnlo : 2*height p a+2 ≤ n := by rcases ha.2 with h | h <;> omega
  have hnhi : n ≤ 2*height p a+3 := by rcases ha.2 with h | h <;> omega
  have hf : (fixedPositions (permutation p a)).card ≤ 2 := by rcases ha.2 with h | h <;> omega
  have hchoose : ∃ b : Fin n,∃ t j : ℕ,t ≤ 2 ∧ j ≤ 2 ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b=height p a ∨ height p b=height p a+1) ∧
      inversions (displacement p b)=inversions (displacement p a)+j ∧
      p 0 ≠ p b-b ∧
      (height p b=height p a+1 →
        (fixedPositions (permutation p a)).card=2 ∧ t=1 ∧ n=2*height p a+3) := by
    by_cases hhead : p 0=p a-a
    · obtain ⟨b,t,j,ht,hj,hoff,hheight,hh,hI,_,_⟩ := unpaid_critical_successor hn4 p a ha hunpaid
      have htv : (t : Fin n).val=t := by simp [Nat.mod_eq_of_lt (by omega : t < n)]
      have hheadb : p 0 ≠ p b-b := by
        intro he
        have ht0 : (t : Fin n)=0 := by
          have hh : (p a-a)+(t : Fin n)=(p a-a)+0 := by
            simpa only [add_zero] using hoff.symm.trans (he.symm.trans hhead)
          exact add_left_cancel hh
        have hv := congrArg Fin.val ht0
        rw [htv,Fin.val_zero] at hv
        omega
      refine ⟨b,t,j,by omega,by omega,hoff,hh,hI,hheadb,?_⟩
      intro hrise
      have hf2 : (fixedPositions (permutation p a)).card=2 := by omega
      have ht1 : t=1 := by omega
      have hodd : n=2*height p a+3 := by rcases ha.2 with h | h <;> omega
      exact ⟨hf2,ht1,hodd⟩
    · exact ⟨a,0,0,by omega,by omega,by simp,Or.inl rfl,by simp,hhead,by omega⟩
  obtain ⟨b,t,j,ht,hj,hoff,hh,hI,hhead,hrise⟩ := hchoose
  obtain ⟨c,hcb,hch,hcd,hlast⟩ := last_offset_source p b
  have hcoff : p c-c=p a-a+(t : Fin n) := hcb.trans hoff
  have hcI : inversions (displacement p c)=inversions (displacement p a)+j := by rw [hcd,hI]
  have hchead : p 0 ≠ p c-c := fun he => hhead (he.trans hcb)
  have hcHeight : height p c=height p a ∨ height p c=height p a+1 := by omega
  have hfinish : 11 ≤ c.val+(-p c).val := by
    by_contra hnot
    rcases hcHeight with hsame | hhigher
    · have hn : n=2*height p c+2 ∨ n=2*height p c+3 := by
        rcases ha.2 with h | h <;> omega
      exact hunpaid (lower_last_corner_upper_word p c hn22 hn hlast (by omega))
    · obtain ⟨hf2,ht1,hodd⟩ := hrise (by omega)
      have hcGap : (c-p c).val ≤ 10 := by
        have hle : (c-p c).val ≤ c.val+(-p c).val := by
          rw [sub_eq_add_neg,Fin.val_add]
          exact Nat.mod_le _ _
        omega
      have he : a-p a=(c-p c)+(t : Fin n) := by linear_combination hcoff
      have htv : (t : Fin n).val=1 := by rw [ht1]; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have hv : (a-p a).val=(c-p c).val+1 := by
        rw [he,Fin.val_add,htv,Nat.mod_eq_of_lt (by omega)]
      exact hunpaid (odd_two_fixed_small_gap_upper_word p a hn4 hodd hf2.le (by omega) (by omega))
  have hcounts := near_two_depth_counts ha.1 c (by omega) (by omega) (by omega) (by omega :
    inversions (displacement p c) ≤ inversions (displacement p a)+2)
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p c (by omega) (by omega) hchead hlast
    (hcounts.2.trans hfinish)
  refine ⟨c,j,hj,hcHeight,hcI,hfinish,hchead,hlast,w,hw,?_⟩
  rw [hcI,Nat.cast_add] at hprice
  linarith

#print axioms unpaid_critical_priced_word
end LX.AnchoredPhases
