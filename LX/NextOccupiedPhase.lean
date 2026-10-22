import LX.OneFixedPhaseChain

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem offset_zero_iff_source_fixed (p : State n) (a i : Fin n) :
    cyclicOffset p a i=0 ↔ permutation p a i=i := by
  rw [cyclic_offset_normalized,sub_eq_zero]

/-- The next occupied raw offset wraps exactly the current fixed positions.
This gives exact height and exchange changes for the original permutation,
including phases which are not globally minimal. -/
theorem next_occupied_phase_with_order (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      (∀ i : Fin n,0 < (cyclicOffset p a i).val → t ≤ (cyclicOffset p a i).val) ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  classical
  let F := fixedPositions (permutation p a)
  let S := Finset.univ.filter fun i => 0 < (cyclicOffset p a i).val
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hh
    have hmove : permutation p a i ≠ i := by
      have hlt := (mem_descendingPositions _ _).mp hi
      intro he
      rw [he] at hlt
      omega
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have hne : cyclicOffset p a i ≠ 0 := fun h => hmove ((offset_zero_iff_source_fixed p a i).mp h)
    exact Fin.pos_iff_ne_zero.mpr hne
  obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image S (fun i => (cyclicOffset p a i).val) hS
  let t := (cyclicOffset p a b).val
  have ht : 0 < t := (Finset.mem_filter.mp hb).2
  have htn : t < n := (cyclicOffset p a b).isLt
  have hbelow (i : Fin n) : (cyclicOffset p a i).val < t ↔ i ∈ F := by
    have hz : (cyclicOffset p a i).val=0 ↔ i ∈ F := by
      have hv : (cyclicOffset p a i).val=0 ↔ cyclicOffset p a i=0 := by
        constructor
        · exact fun h => Fin.ext h
        · exact fun h => congrArg Fin.val h
      rw [hv,offset_zero_iff_source_fixed]
      exact (mem_fixedPositions _ _).symm
    constructor
    · intro hi
      apply hz.mp
      by_contra hnot
      have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      have hbi := hbmin i him
      omega
    · intro hi
      rw [hz.mpr hi]
      exact ht
  have hcount : belowCount p a t=F.card := by
    unfold belowCount
    congr 1
    apply Finset.ext
    intro i
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hbelow i
  have hheight := reanchor_height p a b
  change (height p b : ℤ)=(height p a : ℤ)-(t : ℤ)+belowCount p a t at hheight
  rw [hcount] at hheight
  have hFle : F.card ≤ n := (Finset.card_le_univ F).trans_eq (Fintype.card_fin n)
  have hcard : Fᶜ.card=n-F.card := by rw [Finset.card_compl,Fintype.card_fin]
  have heq : displacement p b=phaseShift (displacement p a) Fᶜ := by
    funext i
    rw [displacement_offset,cyclic_offset_reanchor p a b i,cyclic_subtraction_value]
    unfold phaseShift
    rw [hcard,Nat.cast_sub hFle,displacement_offset]
    by_cases hi : i ∈ F
    · have hb := (hbelow i).mpr hi
      change (cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_true,Finset.mem_compl,hi,not_true_eq_false,ite_false]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+(n : ℤ))-(height p b : ℤ)=_
      omega
    · have hb : ¬(cyclicOffset p a i).val < t := fun hb => hi ((hbelow i).mp hb)
      change ¬(cyclicOffset p a i).val < (cyclicOffset p a b).val at hb
      simp only [hb,ite_false,Finset.mem_compl,hi,not_false_eq_true,ite_true]
      change ((cyclicOffset p a i : ℤ)-(t : ℤ)+0)-(height p b : ℤ)=_
      omega
  have htop : ∀ i ∈ Fᶜ,∀ j ∉ Fᶜ,displacement p a j ≤ displacement p a i := by
    intro i _ j hj
    have hj' : j ∈ F := by simpa using hj
    rw [fixed_source_displacement p a j hj']
    have hb := (displacement_band p a i).1
    omega
  have hsum : (∑ i ∈ Fᶜ,displacement p a i)=(F.card : ℤ)*height p a := by
    have hFsum : (∑ i ∈ F,displacement p a i)= -((F.card : ℤ)*height p a) := by
      calc
        _ = ∑ _i ∈ F,-(height p a : ℤ) := Finset.sum_congr rfl
          (fun i hi => fixed_source_displacement p a i hi)
        _ = _ := by simp
    have hs := Finset.sum_compl_add_sum F (displacement p a)
    rw [hFsum,displacement_balance] at hs
    omega
  have hI := top_phase_inversions (is_lift p a) Fᶜ (displacement_strict_width p a) htop
  rw [← heq,hcard,Nat.cast_sub hFle,hsum] at hI
  refine ⟨b,t,ht,htn,?_,?_,by change _=_+(F.card : ℤ)-_; omega,?_⟩
  · intro i hi
    exact hbmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  · have ho : cyclicOffset p a b=(t : Fin n) := by simp [t]
    unfold cyclicOffset at ho
    linear_combination ho
  · change _=(F.card : ℤ)*_
    nlinarith

theorem next_occupied_phase (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  obtain ⟨b,t,ht,htn,_,hoff,hhb,hI⟩ := next_occupied_phase_with_order p a hh
  exact ⟨b,t,ht,htn,hoff,hhb,hI⟩

/-- Minimum height bounds the next raw step by the fixed multiplicity;
wrapping that multiplicity can increase height and is not silently treated
as another minimum-height phase. -/
theorem minimum_height_next_occupied_phase (p : State n) (a : Fin n)
    (hh : 0 < height p a) (hmin : ∀ b,height p a ≤ height p b) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t ≤ f ∧ t < n ∧
      p b-b=p a-a+(t : Fin n) ∧ height p b+t=height p a+f ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by
  obtain ⟨b,t,ht,htn,hoff,hhb,hI⟩ := next_occupied_phase p a hh
  have hb := hmin b
  exact ⟨b,t,ht,by omega,htn,hoff,by omega,hI⟩

#print axioms next_occupied_phase
#print axioms minimum_height_next_occupied_phase

/-- In the even remaining branch, wrapping a multiple fixed set never
increases the exchange count, but can increase height. -/
theorem even_multiple_fixed_next_phase (p : State n) (a : Fin n)
    (hh : 0 < height p a) (hn : n=2*height p a+2)
    (hmin : ∀ b,height p a ≤ height p b)
    (hf : 2 ≤ (fixedPositions (permutation p a)).card) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t ≤ f ∧ t < n ∧
      p b-b=p a-a+(t : Fin n) ∧ height p b+t=height p a+f ∧
      (inversions (displacement p b) : ℤ)+(f : ℤ)*(f-2)=
        inversions (displacement p a) ∧
      inversions (displacement p b) ≤ inversions (displacement p a) := by
  obtain ⟨b,t,ht,htf,htn,hoff,hheight,hI⟩ := minimum_height_next_occupied_phase p a hh hmin
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have hprod : 0 ≤ ((fixedPositions (permutation p a)).card : ℤ)*
      (((fixedPositions (permutation p a)).card : ℤ)-2) := mul_nonneg (by positivity) (by omega)
  refine ⟨b,t,ht,htf,htn,hoff,hheight,by nlinarith,by nlinarith⟩

/-- Two fixed positions preserve exchanges exactly. The next occupied
offset is one or two, and these alternatives have different heights. -/
theorem even_two_fixed_next_height (p : State n) (a : Fin n)
    (hh : 0 < height p a) (hn : n=2*height p a+2)
    (hmin : ∀ b,height p a ≤ height p b)
    (hf : (fixedPositions (permutation p a)).card=2) :
    ∃ b : Fin n,inversions (displacement p b)=inversions (displacement p a) ∧
      ((p b-b=p a-a+1 ∧ height p b=height p a+1) ∨
       (p b-b=p a-a+2 ∧ height p b=height p a)) := by
  obtain ⟨b,t,ht,htf,_,hoff,hheight,hI,_⟩ := even_multiple_fixed_next_phase p a hh hn hmin (by omega)
  rw [hf] at htf hheight hI
  norm_num only [Nat.cast_ofNat] at hI
  refine ⟨b,by omega,?_⟩
  have hcases : t=1 ∨ t=2 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl ⟨by simpa using hoff,by omega⟩
  · exact Or.inr ⟨by simpa using hoff,by omega⟩

/-- If the successor has reached the global exchange minimum, the unpaid
even hypothesis forces it back to the lower height. A height increase
therefore retains strictly positive excess exchange cost. -/
theorem even_unpaid_height_rise_positive_excess {p : State n} {a b c : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32)
    (hb : height p b+1=m) (hrise : height p b < height p c)
    (k : ℕ) (hf : (inversions (displacement p c) : ℤ)+
      ((fixedPositions (permutation p b)).card : ℤ)*
        (((fixedPositions (permutation p b)).card : ℤ)-2)=
          inversions (displacement p a)+k) :
    ((fixedPositions (permutation p b)).card : ℤ)*
        (((fixedPositions (permutation p b)).card : ℤ)-2) < k := by
  have hc := global_minimum_exchanges ha c
  have hne : inversions (displacement p c) ≠ inversions (displacement p a) := by
    intro he
    have hcg := global_minimum_of_equal_exchanges ha he
    have hh := even_unpaid_global_height hn4 m hn hcg hunpaid
    omega
  omega

#print axioms even_multiple_fixed_next_phase
#print axioms even_two_fixed_next_height
#print axioms even_unpaid_height_rise_positive_excess

/-- A same-height multiple step improves the exact orientation-minus-reserve
price by f*(f-1), provided it has not crossed the orientation seam. -/
theorem even_same_height_cyclic_price (p : State n) (a b : Fin n) (f : ℕ)
    (hh : height p b=height p a)
    (hoff : p b-b=p a-a+(f : Fin n))
    (hI : (inversions (displacement p b) : ℤ)+(f : ℤ)*(f-2)=
      inversions (displacement p a))
    (hgap : f ≤ (a-p a).val) :
    ((b-p b).val : ℤ)-anchorReserve p b=
      ((a-p a).val : ℤ)-anchorReserve p a-(f : ℤ)*(f-1) := by
  have hfn : f < n := lt_of_le_of_lt hgap (a-p a).isLt
  have hfv : (f : Fin n).val=f := by simp [Nat.mod_eq_of_lt hfn]
  have hback : b-p b=a-p a-(f : Fin n) := by linear_combination -hoff
  have hle : (f : Fin n) ≤ a-p a := by change (f : Fin n).val ≤ (a-p a).val; rwa [hfv]
  have hv : (b-p b).val=(a-p a).val-f := by rw [hback,Fin.coe_sub_iff_le.mpr hle,hfv]
  rw [hv,Nat.cast_sub hgap]
  unfold anchorReserve
  rw [hh]
  nlinarith

/-- Connect the singleton-chain reduction to its actual next phase. The
exchange refund is exact even when the successor leaves minimum height. -/
theorem even_unpaid_multiple_phase_successor (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a b c : Fin n,∃ k t : ℕ,GlobalMinimum p a ∧ 0 < k ∧
      2 ≤ (fixedPositions (permutation p b)).card ∧ height p b+1=m ∧
      (∀ d,height p b ≤ height p d) ∧
      inversions (displacement p b)=inversions (displacement p a)+k ∧
      0 < t ∧ t ≤ (fixedPositions (permutation p b)).card ∧
      p c-c=p b-b+(t : Fin n) ∧
      height p c+t=height p b+(fixedPositions (permutation p b)).card ∧
      (inversions (displacement p c) : ℤ)+
        ((fixedPositions (permutation p b)).card : ℤ)*
          (((fixedPositions (permutation p b)).card : ℤ)-2)=
            inversions (displacement p a)+k ∧
      anchorReserve p b+31 ≤ ((b-p b).val : ℤ) ∧
      (height p b < height p c →
        ((fixedPositions (permutation p b)).card : ℤ)*
          (((fixedPositions (permutation p b)).card : ℤ)-2) < k) := by
  obtain ⟨a,b,k,ha,_,hk,hf,hh,hmin,hI,_,_,_,hgap,_,_⟩ :=
    even_unpaid_multiple_fixed_phase hn4 p m hn hunpaid
  have hpos : 0 < height p b := by omega
  obtain ⟨c,t,ht,htf,_,hoff,hheight,hIc,_⟩ :=
    even_multiple_fixed_next_phase p b hpos (by omega) hmin hf
  have hprice : (inversions (displacement p c) : ℤ)+
      ((fixedPositions (permutation p b)).card : ℤ)*
        (((fixedPositions (permutation p b)).card : ℤ)-2)=
          inversions (displacement p a)+k := by
    rw [hI,Nat.cast_add] at hIc
    exact hIc
  exact ⟨a,b,c,k,t,ha,hk,hf,hh,hmin,hI,ht,htf,hoff,hheight,hprice,hgap,
    fun hrise => even_unpaid_height_rise_positive_excess hn4 m hn ha hunpaid hh hrise k hprice⟩

#print axioms even_same_height_cyclic_price
#print axioms even_unpaid_multiple_phase_successor
end LX.AnchoredPhases
