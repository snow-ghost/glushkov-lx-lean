import LX.SharpScanDeletion
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_reflection_sharp_zero_word (p : State n) (r a : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 4 ≤ m)
    (ha : m < a.val) (hfinish : a.val+(-p a).val ≤ n+3) :
    ∃ w : List Letter,p*eval w=1 ∧ (∀ i,run w (displacement p a) i=0) ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+16 := by
  have hall (a : Fin n) : height p a=m-1 := reflection_height_even p r hp m hn (by omega) a
  have hF (a : Fin n) : (fixedPositions (permutation p a)).card ≤ 2 := by
    have hc := top_depth_count (is_lift p a)
      (global_minimum_majorized (reflection_global_minimum p r hp a))
      (height p a) (by have := hall a; omega)
      (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    rw [top_depth_count_eq_fixed] at hc
    have := hall a
    omega
  obtain ⟨hdepthhead,hlastdepth⟩ := reflection_depth_positions_even p r hp m hn (by omega) a ha
  have hfixed (i : Fin n) (hi : p i-i=p a-a) : permutation p a i=i := by
    change p i+(a-p a)=i
    linear_combination hi
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hd := (depth_eq_height_iff_fixed p a 0).mpr (hfixed 0 (by simpa using he))
    omega
  have hlast (i : Fin n) (hi : p i-i=p a-a) : i.val ≤ a.val :=
    hlastdepth i ((depth_eq_height_iff_fixed p a i).mpr (hfixed i hi))
  have hc := constant_height_next_depth p (m-1) 2 hall hF (by omega) a
  have hh := hall a
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by
    rw [hh]
    omega
  obtain ⟨w,hw,hzero,hprice⟩ := aligned_anchor_exact_zero_word p a (by omega) (by omega) hhead hlast hcount
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
  have hf : (a.val : ℤ)+((-p a).val : ℤ) ≤ (n : ℤ)+3 := by exact_mod_cast hfinish
  exact ⟨w,hw,hzero,by nlinarith only [hprice,hcap,hn',hf]⟩

theorem even_reflection_sharp_crossing_choice (p : State n) (r i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m) (hm : 4 ≤ m) :
    (∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+3 ∧
      2 ≤ (cyclicOffset p a i).val) ∨
      (r=0 ∧ (i.val=1 ∨ i.val=m+1)) := by
  have hneg (j : Fin n) : -p j=j-r := by rw [hp]; abel
  have hdouble : (m : Fin n)+(m : Fin n)=0 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    simp only [Nat.cast_mul,Nat.cast_ofNat,Fin.natCast_self] at he
    linear_combination -he
  by_cases hr0 : r=0
  · let a : Fin n := ⟨m+1,by omega⟩
    have hav : a.val=m+1 := rfl
    have hfinish : a.val+(-p a).val ≤ n+3 := by
      rw [hneg,hr0,sub_zero]
      omega
    by_cases hcross : 2 ≤ (cyclicOffset p a i).val
    · exact Or.inl ⟨a,by omega,hfinish,hcross⟩
    have heven : Even (cyclicOffset p a i) := by
      refine ⟨a-i,?_⟩
      unfold cyclicOffset
      simp only [hp]
      ring
    have hmod := (Fin.even_iff_mod_of_even (show Even n from ⟨m,by omega⟩)).mp heven
    have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have htwice : i+i=a+a := by
      unfold cyclicOffset at hz
      simp only [hp] at hz
      linear_combination -hz
    have hcases := doubled_residue_cases i a htwice
    have hi := i.isLt
    exact Or.inr ⟨hr0,by omega⟩
  by_cases hrlast : r.val=n-1
  · let a : Fin n := ⟨m+1,by omega⟩
    have hav : a.val=m+1 := rfl
    have hfinish : a.val+(-p a).val ≤ n+3 := by
      rw [hneg,Fin.coe_sub_iff_lt.mpr (show a < r from by change a.val < r.val; omega)]
      omega
    have hfinishr : r.val+(-p r).val ≤ n+3 := by simp [hp]; have := r.isLt; omega
    by_cases hcross : 2 ≤ (cyclicOffset p a i).val
    · exact Or.inl ⟨a,by omega,hfinish,hcross⟩
    have hcrossr : 2 ≤ (cyclicOffset p r i).val := by
      by_contra hnot
      have hrfin : r+1=0 := by
        have he : ((r.val+1 : ℕ) : Fin n)=0 := by rw [show r.val+1=n by omega]; simp
        simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one] using he
      have hafin : a=(m : Fin n)+1 := by
        apply Fin.ext
        change m+1=(m%n+1%n)%n
        rw [Nat.mod_eq_of_lt (by omega : m<n),Nat.mod_eq_of_lt (by omega : 1<n),Nat.mod_eq_of_lt (by omega)]
      have he : cyclicOffset p a i=cyclicOffset p r i+4 := by
        unfold cyclicOffset
        simp only [hp,hafin]
        linear_combination hdouble-2*hrfin
      have hv := congrArg Fin.val he
      have hv4 : (4 : Fin n).val=4 := by norm_num [Nat.mod_eq_of_lt (by omega : 4<n)]
      rw [Fin.val_add,hv4,Nat.mod_eq_of_lt (by omega)] at hv
      omega
    exact Or.inl ⟨r,by omega,hfinishr,hcrossr⟩
  · let a : Fin n := ⟨max (m+1) r.val,by have := r.isLt; omega⟩
    have hav : a.val=max (m+1) r.val := rfl
    have hbval : (a+1).val=max (m+1) r.val+1 := by
      rw [Fin.val_add_one_of_lt' (by have := r.isLt; omega : a.val+1<n),hav]
    have hrpos : 0 < r.val := Fin.pos_iff_ne_zero.mpr hr0
    have hgood (j : Fin n) (hj : j.val=max (m+1) r.val ∨ j.val=max (m+1) r.val+1) :
        m < j.val ∧ j.val+(-p j).val ≤ n+3 := by
      have hjr : r ≤ j := by change r.val ≤ j.val; omega
      rw [hneg,Fin.coe_sub_iff_le.mpr hjr]
      have := r.isLt
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact Or.inl ⟨b,hg.1,hg.2,hcross⟩

#print axioms even_reflection_sharp_zero_word
#print axioms even_reflection_sharp_crossing_choice
end LX.AnchoredPhases
