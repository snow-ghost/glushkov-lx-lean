import LX.ExchangeReserve
import LRX.CapacityEqualityReflection

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- All anchored phases of a circular reflection differ by relabelling the
positions. In particular their energies agree, including in even dimension. -/
theorem reflection_offset_rotate (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a b i : Fin n) :
    cyclicOffset p b (i+(b-a))=cyclicOffset p a i := by
  unfold cyclicOffset
  simp only [hp]
  ring

theorem reflection_height_eq (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a b : Fin n) : height p b=height p a := by
  have hs := Equiv.sum_comp (Equiv.addRight (b-a))
    (fun i : Fin n => (cyclicOffset p b i : ℤ))
  change (∑ i : Fin n,(cyclicOffset p b (i+(b-a)) : ℤ))=∑ i : Fin n,(cyclicOffset p b i : ℤ) at hs
  simp_rw [reflection_offset_rotate p r hp a b] at hs
  rw [cyclic_offset_mass,cyclic_offset_mass] at hs
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have he : (height p a : ℤ)=height p b := by nlinarith
  omega

theorem reflection_displacement_rotate (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a b i : Fin n) :
    displacement p b (i+(b-a))=displacement p a i := by
  rw [displacement_offset,displacement_offset,reflection_offset_rotate p r hp a b,
    reflection_height_eq p r hp a b]

theorem reflection_energy_eq (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a b : Fin n) : energy (displacement p b)=energy (displacement p a) := by
  have hs := Equiv.sum_comp (Equiv.addRight (b-a))
    (fun i : Fin n => (displacement p b i).natAbs^2)
  change (∑ i : Fin n,(displacement p b (i+(b-a))).natAbs^2)=energy (displacement p b) at hs
  simp_rw [reflection_displacement_rotate p r hp a b] at hs
  exact hs.symm

theorem reflection_global_minimum (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a : Fin n) : GlobalMinimum p a := by
  obtain ⟨b,hb⟩ := exists_global_minimum p
  intro c d hd
  rw [reflection_energy_eq p r hp b a]
  exact hb c d hd

/-- Equality of doubled residues has only the three possible integer lifts.
This handles both parity cases without assuming that 2 is invertible. -/
theorem doubled_residue_cases (i j : Fin n) (he : i+i=j+j) :
    2*i.val=2*j.val ∨ 2*i.val+n=2*j.val ∨ 2*j.val+n=2*i.val := by
  have hwrap (x : Fin n) : (x+x).val=if 2*x.val<n then 2*x.val else 2*x.val-n := by
    change (x.val+x.val)%n=_
    have hx := x.isLt
    by_cases hh : 2*x.val<n
    · rw [ite_eq_left hh,Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [ite_eq_right hh,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
  have hv := congrArg Fin.val he
  rw [hwrap,hwrap] at hv
  split_ifs at hv <;> omega

theorem reflection_complete_odd (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m+1) : CompleteMapping p := by
  intro i j hij
  have he : i+i=j+j := by
    simp only [hp] at hij
    linear_combination -hij
  have hc := doubled_residue_cases i j he
  apply Fin.ext
  omega

/-- The missing endpoint of an even reflection's displacement range determines
its height exactly; the shortness premise is supplied by an actual minimum. -/
theorem reflection_height_even (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 2 ≤ m) (a : Fin n) :
    height p a=m-1 := by
  have hmajor := global_minimum_majorized (reflection_global_minimum p r hp a)
  have hlo := (short_coordinates (is_lift p a).1 hmajor a).2
  rw [displacement_anchor] at hlo
  have he : cyclicOffset p a (a+1)= -(2 : Fin n) := by
    unfold cyclicOffset
    simp only [hp]
    ring
  have hv : (-(2 : Fin n)).val=n-2 := by
    have hn2 : 2 < n := by omega
    have hne : (2 : Fin n) ≠ 0 := by
      intro hh
      have hv := congrArg Fin.val hh
      norm_num [Nat.mod_eq_of_lt hn2] at hv
    simp [Fin.val_neg,hne,Nat.mod_eq_of_lt hn2]
  have hhi := (short_coordinates (is_lift p a).1 hmajor (a+1)).1
  rw [displacement_offset,he] at hhi
  change 2*((((-(2 : Fin n)).val : ℕ) : ℤ)-(height p a : ℤ)) ≤ (n : ℤ)-1 at hhi
  rw [hv] at hhi
  omega

theorem reflection_depth_positions_even (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 2 ≤ m)
    (a : Fin n) (ha : m < a.val) :
    backwardDepth (displacement p a) 0 < height p a ∧
      ∀ i,backwardDepth (displacement p a) i=height p a → i.val ≤ a.val := by
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  have hc (i : Fin n) (hi : backwardDepth (displacement p a) i=height p a) :
      2*i.val=2*a.val ∨ 2*i.val+n=2*a.val ∨ 2*a.val+n=2*i.val := by
    have hd := maximum_depth_displacement (is_lift p a) i
      (by intro j; rw [hi]; exact hmax j)
    rw [hi,displacement_offset] at hd
    have hz : cyclicOffset p a i=0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    have he : i+i=a+a := by
      unfold cyclicOffset at hz
      simp only [hp] at hz
      linear_combination -hz
    exact doubled_residue_cases i a he
  constructor
  · have hb := hmax 0
    by_contra hnot
    have hh := hc 0 (by omega)
    simp only [Fin.val_zero] at hh
    omega
  · intro i hi
    have hh := hc i hi
    have hn' := i.isLt
    omega

/-- For an even reflection the chosen late anchor bounds every maximal-depth
position, and a small final phase residue pays the desired linear term. -/
theorem reflection_anchor_zero_word_even (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 10 ≤ m)
    (a : Fin n) (ha : m < a.val) (R : ℕ)
    (hfinish : a.val+(-p a).val ≤ n+R) :
    ∃ w : List Letter,p*eval w=1 ∧ (∀ i,run w (displacement p a) i=0) ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+4*((R : ℤ)+1) := by
  let h := height p a
  have heighth : h=m-1 := reflection_height_even p r hp m hn (by omega) a
  have hn2 : 2 ≤ n := by omega
  have hpos : 2 ≤ h := by omega
  have hap : 0 < a.val := by omega
  have hd := is_lift p a
  have hmajor := global_minimum_majorized (reflection_global_minimum p r hp a)
  have hl (i : Fin n) : labels (displacement p a) i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hinj : Function.Injective (labels (displacement p a)) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  obtain ⟨hhead,hpositions⟩ := reflection_depth_positions_even p r hp m hn (by omega) a ha
  have ht := majorized_scan_deadline hn2 hd hmajor hinj h a.val hpos (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead hpositions
  have hcount : 3*(n-2*h)+2=8 := by omega
  rw [hcount,max_eq_left (by omega : 8 ≤ a.val)] at ht
  let T := (h-1)*(n-1)+(a.val-1)+(-p a).val
  have hT : scanDeadline (displacement p a) ≤ T := by dsimp [T]; omega
  have hcast : (T : Fin n)=(phase p a : Fin n) := by
    dsimp only [T,phase,h]
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ height p a),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  obtain ⟨w,htw,_⟩ := candidate_sorting_word hn2 p a
  obtain ⟨v,hv,hzero,hlen⟩ := htw.word_at_cursor_zero hn2 p (phase p a : Fin n) hd.1 hinj hl T
    ((htw.rotations_le_deadline hn2 hd.1 hinj).trans hT)
  rw [hcast,sub_self,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=((h : ℤ)-1)*((n : ℤ)-1)+(a.val : ℤ)-1+((-p a).val : ℤ) := by
    dsimp only [T]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    ring
  have hx := (candidate_price_components p a).1
  change (inversions (displacement p a) : ℤ) ≤ (h : ℤ)*((n : ℤ)-h-1) at hx
  have hlen' : (v.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hn' : (n : ℤ)=2*(h : ℤ)+2 := by omega
  have hf : (a.val : ℤ)+((-p a).val : ℤ) ≤ (n : ℤ)+R := by exact_mod_cast hfinish
  exact ⟨v,hv,hzero,by nlinarith⟩

theorem reflection_anchor_word_even (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 10 ≤ m)
    (a : Fin n) (ha : m < a.val)
    (hfinish : a.val+(-p a).val ≤ n+2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  obtain ⟨w,hw,_,hprice⟩ := reflection_anchor_zero_word_even p r hp m hn hm a ha 2 hfinish
  exact ⟨w,hw,by simpa using hprice⟩

/-- A literal LX upper bound for every circular reflection, including the
even family which is not a complete mapping. -/
theorem reflection_upper_word (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases hsmall : n < 22
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn p⁻¹
    refine ⟨w,?_,?_⟩
    · rw [hw,mul_inv_cancel]
    · have hs : (n : ℤ)<22 := by omega
      nlinarith
  · by_cases heven : n=2*(n/2)
    · let m := n/2
      have hm : 10 ≤ m := by dsimp [m]; omega
      have hgood : ∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+2 := by
        by_cases hr : m < r.val
        · refine ⟨r,hr,?_⟩
          simp only [hp,sub_self,neg_zero,Fin.val_zero,add_zero]
          have := r.isLt
          omega
        · let a : Fin n := ⟨m+1,by dsimp [m] at *; omega⟩
          refine ⟨a,by dsimp [a]; omega,?_⟩
          have he : -p a=a-r := by rw [hp]; abel
          rw [he,Fin.coe_sub_iff_le.mpr (show r ≤ a by change r.val ≤ a.val; dsimp [a]; omega)]
          dsimp [a,m]
          omega
      obtain ⟨a,ha,hfinish⟩ := hgood
      obtain ⟨w,hw,hprice⟩ := reflection_anchor_word_even p r hp m heven hm a ha hfinish
      exact ⟨w,hw,by omega⟩
    · exact complete_mapping_upper_word p
        (reflection_complete_odd p r hp (n/2) (by omega)) hn

#print axioms reflection_global_minimum
#print axioms reflection_complete_odd
#print axioms reflection_height_even
#print axioms reflection_anchor_zero_word_even
#print axioms reflection_upper_word
end LX.AnchoredPhases
