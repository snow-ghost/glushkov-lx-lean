import LX.AnchorPhasePrice
import LX.AnchorReserveRigidity
import LX.CrowdedDeadline
import LX.EvenSecondHeight
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Exact exchange price at an orientation-aligned deadline. Only the
actual next-depth count is needed; majorization of this anchor is not assumed. -/
theorem aligned_anchor_exact_word (p : State n) (a : Fin n)
    (hh : 2 ≤ height p a) (hn : 2 ≤ n)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val) :
    ∃ w : List Letter,p*eval w=1 ∧
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
  obtain ⟨v,hv,hlen⟩ := htw.word_at_cursor hn p (phase p a : Fin n) hd.1 hinj hl T
    ((htw.rotations_le_deadline hn hd.1 hinj).trans hT)
  rw [hcast,sub_self,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=((h : ℤ)-1)*((n : ℤ)-1)+(a.val : ℤ)-1+((-p a).val : ℤ) := by
    dsimp only [T]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    ring
  have hlen' : (v.length : ℤ)=(inversions d : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  exact ⟨v,hv,by rw [hlen',hTi]; dsimp only [d,h]; ring⟩

/-- At even maximal height, the complete strip reserve is retained as
a subtraction from the word price, including for nonminimal phases. -/
theorem even_anchor_reserve_price (p : State n) (a : Fin n)
    (hh : 2 ≤ height p a) (hn : n=2*height p a+2)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((a.val : ℤ)+((-p a).val : ℤ)-(n : ℤ)+1-anchorReserve p a) := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p a hh (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  nlinarith

/-- At the remaining odd height, both the lower height and the exact
strip reserve contribute to payment. -/
theorem odd_lower_anchor_reserve_price (p : State n) (a : Fin n)
    (hh : 2 ≤ height p a) (hn : n=2*height p a+3)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((a.val : ℤ)+((-p a).val : ℤ)-(n : ℤ)-height p a-anchorReserve p a)-3 := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p a hh (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
  nlinarith


#print axioms aligned_anchor_exact_word
end LX.AnchoredPhases
