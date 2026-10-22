import LX.NextOccupiedPhase

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- At the raised even height, the two top depth counts are controlled by
the square root of the actual exchange excess, rather than by 3*K. -/
theorem even_higher_depth_counts {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n) (K R : ℕ)
    (hn : n=2*height p b) (hh : 0 < height p b)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hKR : K ≤ R^2) :
    depthCount (displacement p b) (height p b) ≤ R ∧
      depthCount (displacement p b) (height p b-1) ≤ 3*R+2 := by
  let d := displacement p b
  let h := height p b
  have hd := is_lift p b
  have hm := near_majorized_of_exchange_allowance ha b K hx
  have hwidth (i j : Fin n) : d i-d j ≤ (n : ℤ) := (displacement_strict_width p b i j).le
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have hi := (candidate_price_components p b).2 i
    change (backwardDepth d i : ℤ) ≤ (h : ℤ) at hi
    change ¬h+1 ≤ backwardDepth d i
    omega
  have htop := near_depth_count_quadratic hd hm hwidth h
  change (depthCount d h : ℤ)*((depthCount d h : ℤ)-(n : ℤ)+2*h-
    2*depthCount d (h+1)) ≤ K at htop
  rw [hz,Nat.cast_zero,mul_zero,sub_zero] at htop
  have hn' : (n : ℤ)=2*(h : ℤ) := by exact_mod_cast hn
  have hKR' : (K : ℤ) ≤ (R : ℤ)^2 := by exact_mod_cast hKR
  have hf : depthCount d h ≤ R := by
    by_contra hnot
    have hp := mul_nonneg (show 0 ≤ (depthCount d h : ℤ)-(R : ℤ)-1 by omega)
      (show 0 ≤ (depthCount d h : ℤ)+(R : ℤ)+1 by positivity)
    nlinarith
  have hnext := near_depth_count_quadratic hd hm hwidth (h-1)
  have hs : h-1+1=h := by dsimp [h]; omega
  rw [hs] at hnext
  change (depthCount d (h-1) : ℤ)*((depthCount d (h-1) : ℤ)-(n : ℤ)+
    2*((h-1 : ℕ) : ℤ)-2*depthCount d h) ≤ K at hnext
  rw [Nat.cast_sub (by dsimp [h]; omega : 1 ≤ h),Nat.cast_one] at hnext
  refine ⟨hf,?_⟩
  change depthCount d (h-1) ≤ 3*R+2
  by_contra hnot
  have hlow : 3*(R : ℤ)+3 ≤ depthCount d (h-1) := by omega
  have hrel := mul_nonneg (show 0 ≤ (depthCount d (h-1) : ℤ) by positivity)
    (show 0 ≤ (R : ℤ)-depthCount d h by omega)
  have hp := mul_nonneg (show 0 ≤ (depthCount d (h-1) : ℤ)-(3*(R : ℤ)+3) by omega)
    (show 0 ≤ (depthCount d (h-1) : ℤ)+(R : ℤ)+1 by positivity)
  nlinarith

/-- The exact word price at height n/2. The terminal allowance must pay
the strip reserve, with no hidden assumption of majorization. -/
theorem even_higher_anchor_reserve_price (p : State n) (b : Fin n)
    (hn4 : 4 ≤ n) (hn : n=2*height p b)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((b.val : ℤ)+((-p b).val : ℤ)-anchorReserve p b) := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p b (by omega) (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p b : ℤ) := by exact_mod_cast hn
  nlinarith

/-- A higher phase is paid whenever its actual orientation allowance lies
between the derived crowding bound and the available exchange reserve. -/
theorem even_higher_near_phase_upper_word {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n) (K R : ℕ)
    (hn4 : 4 ≤ n) (hn : n=2*height p b)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hKR : K ≤ R^2) (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hlo : 3*R+2 ≤ b.val+(-p b).val)
    (hhi : (b.val : ℤ)+((-p b).val : ℤ) ≤ anchorReserve p b+31) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  have hc := (even_higher_depth_counts ha b K R hn (by omega) hx hKR).2
  obtain ⟨w,hw,hprice⟩ := even_higher_anchor_reserve_price p b hn4 hn hhead hlast (hc.trans hlo)
  exact ⟨w,hw,by linarith⟩

/-- Necessary obstruction at any eligible higher successor. Both the
exchange allowance and the finishing positions refer to this actual phase. -/
theorem even_unpaid_higher_finish {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n) (K R : ℕ)
    (hn4 : 4 ≤ n) (hn : n=2*height p b)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hKR : K ≤ R^2) (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hlo : 3*R+2 ≤ b.val+(-p b).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    anchorReserve p b+32 ≤ (b.val : ℤ)+((-p b).val : ℤ) := by
  by_contra hnot
  exact hunpaid (even_higher_near_phase_upper_word ha b K R hn4 hn hx hKR hhead hlast hlo (by omega))

#print axioms even_higher_depth_counts
#print axioms even_higher_anchor_reserve_price
#print axioms even_higher_near_phase_upper_word
#print axioms even_unpaid_higher_finish

/-- At the odd maximal height, retain the full exchange reserve in the
same literal word construction. -/
theorem odd_higher_anchor_reserve_price (p : State n) (b : Fin n)
    (hn4 : 4 ≤ n) (hn : n=2*height p b+1)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((b.val : ℤ)+((-p b).val : ℤ)-height p b-anchorReserve p b)+1 := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p b (by omega) (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p b : ℤ)+1 := by exact_mod_cast hn
  nlinarith

/-- A majorized odd maximal-height source has one fixed position. -/
theorem odd_higher_fixed_unique (p : State n) (b : Fin n)
    (hm : Majorized (displacement p b)) (hn : n=2*height p b+1) :
    (LRX.FiniteCuts.fixedPositions (permutation p b)).card=1 := by
  have hc := top_depth_count (is_lift p b) hm (height p b) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i)
  rw [top_depth_count_eq_fixed] at hc
  have hp : 0 < (LRX.FiniteCuts.fixedPositions (permutation p b)).card := Finset.card_pos.mpr
    ⟨b,(LRX.FiniteCuts.mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
  omega

/-- All scheduling premises at a global odd maximal-height phase are
derived from that phase; only its actual finish allowance is constrained. -/
theorem odd_higher_global_upper_word {p : State n} {b : Fin n}
    (hb : GlobalMinimum p b) (hn4 : 4 ≤ n) (hn : n=2*height p b+1)
    (hb0 : 0 < b.val) (hlo : 5 ≤ b.val+(-p b).val)
    (hhi : (b.val : ℤ)+((-p b).val : ℤ) ≤ height p b+anchorReserve p b+31) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  have hm := global_minimum_majorized hb
  have hf := odd_higher_fixed_unique p b hm hn
  have hhead : p 0 ≠ p b-b := by
    intro he
    have hz := one_fixed_last_offset p b hf 0 (by simpa using he)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hv
    omega
  have hlast (i : Fin n) (hi : p i-i=p b-b) : i.val ≤ b.val := by
    rw [one_fixed_last_offset p b hf i hi]
  have hc := next_depth_count (is_lift p b) hm (height p b) (by omega) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i)
  have hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val := by omega
  obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p b hn4 hn hhead hlast hcount
  exact ⟨w,hw,by linarith⟩

/-- Unpaid maximal-height forward anchors have a short ordinary forward
span. This retains the exchange reserve needed for the remaining odd case. -/
theorem odd_unpaid_higher_forward_span {p : State n} {b : Fin n}
    (hb : GlobalMinimum p b) (hn4 : 4 ≤ n) (hn : n=2*height p b+1)
    (hb0 : 0 < b.val) (hforward : b.val < (p b).val)
    (hlo : 5 ≤ b.val+(-p b).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ((p b).val : ℤ)-(b.val : ℤ)+anchorReserve p b+31 ≤ height p b := by
  have hnot : ¬(b.val : ℤ)+((-p b).val : ℤ) ≤ height p b+anchorReserve p b+31 :=
    fun hh => hunpaid (odd_higher_global_upper_word hb hn4 hn hb0 hlo hh)
  have hne : p b ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
  have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hne]
  rw [hneg,Nat.cast_sub (Nat.le_of_lt (p b).isLt)] at hnot
  omega

#print axioms odd_higher_anchor_reserve_price
#print axioms odd_higher_fixed_unique
#print axioms odd_higher_global_upper_word
#print axioms odd_unpaid_higher_forward_span
end LX.AnchoredPhases
