import LX.ReflectionConjecture
import LX.ReflectionNeighbor

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem aligned_anchor_exact_zero_word (p : State n) (a : Fin n)
    (hh : 2 ≤ height p a) (hn : 2 ≤ n)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val) :
    ∃ w : List Letter,p*eval w=1 ∧ (∀ i,run w (displacement p a) i=0) ∧
      (w.length : ℤ)=(inversions (displacement p a) : ℤ)+
        ((height p a : ℤ)-1)*((n : ℤ)-1)+(a.val : ℤ)-1+((-p a).val : ℤ) := by
  let h := height p a
  let d := displacement p a
  have hap : 0 < a.val := by
    by_contra hnot
    have he : a=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    exact hhead (by simp [he])
  have hd := is_lift p a
  have hl (i : Fin n) : labels d i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hinj : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have hmax (i : Fin n) : backwardDepth d i ≤ h := by
    exact_mod_cast (candidate_price_components p a).2 i
  have hhead' : backwardDepth d 0 < h := by
    apply head_reserve_of_distinct_offset
    intro he
    apply hhead
    simpa only [cyclicOffset,sub_zero,sub_eq_zero] using he
  have hpositions (i : Fin n) (hi : backwardDepth d i=h) : i.val ≤ a.val := by
    have hd' := maximum_depth_displacement hd i (by intro j; rw [hi]; exact hmax j)
    rw [hi,displacement_offset] at hd'
    have hval : (cyclicOffset p a i).val=0 := by omega
    have he : cyclicOffset p a i=0 := Fin.ext hval
    exact hlast i (sub_eq_zero.mp he)
  have ht := scan_deadline_of_crowding hn d hinj h a.val (depthCount d (h-1)) hh
    hmax hhead' hpositions le_rfl
  have hbound : max a.val (depthCount d (h-1)) ≤ a.val+(-p a).val := max_le (by omega) hcount
  let T := (h-1)*(n-1)+(a.val-1)+(-p a).val
  have hT : scanDeadline d ≤ T := by dsimp only [T]; omega
  have hcast : (T : Fin n)=(phase p a : Fin n) := by
    dsimp only [T,phase,h]
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ height p a),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  obtain ⟨w,htw,_⟩ := candidate_sorting_word hn p a
  obtain ⟨v,hv,hzero,hlen⟩ := htw.word_at_cursor_zero hn p (phase p a : Fin n) hd.1 hinj hl T
    ((htw.rotations_le_deadline hn hd.1 hinj).trans hT)
  rw [hcast,sub_self,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=((h : ℤ)-1)*((n : ℤ)-1)+(a.val : ℤ)-1+((-p a).val : ℤ) := by
    dsimp only [T]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    ring
  have hlen' : (v.length : ℤ)=(inversions d : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  exact ⟨v,hv,hzero,by rw [hlen',hTi]; dsimp only [d,h]; ring⟩

theorem complete_anchor_reserve_zero_word (p : State n) (hp : CompleteMapping p)
    (hn : 5 ≤ n) (a : Fin n) (k : ℕ) (ha : 0 < a.val)
    (hforward : a.val+height p a ≤ (p a).val+k)
    (hcorner : 3 ≤ a.val+(n-(p a).val)) (hk : k < height p a) :
    ∃ w : List Letter,p*eval w=1 ∧ (∀ i,run w (displacement p a) i=0) ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+4*(k+1-anchorReserve p a)+1 := by
  let h := height p a
  have hparity : n=2*h+1 := complete_height p hp a
  have hall (a : Fin n) : height p a=h := by
    have := complete_height p hp a
    omega
  have hfixed (a : Fin n) : (fixedPositions (permutation p a)).card=1 :=
    odd_higher_fixed_unique p a (complete_majorized p hp a) (complete_height p hp a)
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hz := one_fixed_last_offset p a (hfixed a) 0 (by simpa using he)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hv
    omega
  have hlast (i : Fin n) (hi : p i-i=p a-a) : i.val ≤ a.val := by
    rw [one_fixed_last_offset p a (hfixed a) i hi]
  have hne : p a ≠ 0 := by
    intro he
    rw [he,Fin.val_zero] at hforward
    omega
  have hneg : (-p a).val=n-(p a).val := by simp [Fin.val_neg,hne]
  have hc := constant_height_next_depth p h 1 hall (fun b => (hfixed b).le) (by omega) a
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by
    rw [hall a,hneg]
    omega
  obtain ⟨w,hw,hzero,hprice⟩ := aligned_anchor_exact_zero_word p a (by omega) (by omega) hhead hlast hcount
  have hres := anchor_reserve_nonneg p a
  rw [hneg,hall a] at hprice
  have hh : height p a=h := rfl
  have hn' : (n : ℤ)=2*(h : ℤ)+1 := by exact_mod_cast hparity
  have hf : (a.val : ℤ)+(n-(p a).val : ℕ) ≤ (h : ℤ)+k+1 := by omega
  have hr : anchorReserve p a=(h : ℤ)*((n : ℤ)-h-1)-inversions (displacement p a) := rfl
  refine ⟨w,hw,hzero,?_⟩
  nlinarith only [hprice,hn',hf,hr]

theorem odd_reflection_crossing_conjecture_word (p : State n) (r a i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m+1) (hm : 3 ≤ m)
    (ha : 0 < a.val) (hforward : a.val+m ≤ (p a).val+2)
    (hcorner : 3 ≤ a.val+(n-(p a).val)) (hcross : 2 ≤ (cyclicOffset p a i).val) :
    ∃ w : List Letter,(p*Equiv.swap i (i+1))*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  have hc := reflection_complete_odd p r hp m hn
  have hh : height p a=m := by have := complete_height p hc a; omega
  obtain ⟨w,hw,hzero,hprice⟩ := complete_anchor_reserve_zero_word p hc (by omega) a 2 ha
    (by omega) hcorner (by omega)
  have hr := anchor_reserve_nonneg p a
  obtain ⟨v,hv,hlen,_⟩ := LX.LiftedScan.delete_adjacent_descent (by omega) p
    (displacement p a) w hw hzero i (reflection_neighbor_descent (by omega) p r hp a i hcross)
  exact ⟨v,hv,by omega⟩

#print axioms aligned_anchor_exact_zero_word
#print axioms complete_anchor_reserve_zero_word
#print axioms odd_reflection_crossing_conjecture_word
end LX.AnchoredPhases
