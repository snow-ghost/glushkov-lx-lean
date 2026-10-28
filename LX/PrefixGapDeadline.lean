import LX.AnchorPhasePrice
import LX.EvenSecondHeight
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem emitted_depth_top_positions_prefix (d : Fin n → ℤ) (h M K : ℕ)
    (hpos : 2 ≤ h) (hmax : ∀ i, backwardDepth d i ≤ h)
    (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i, backwardDepth d i=h → i.val ≤ M)
    (hprefix : ∀ j ≤ n,(∀ i < j,h-1 ≤ atDepth d i) → j ≤ K)
    (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    emittedDepth d j ≤ h-1 ∧
      (emittedDepth d j=h-1 → j ≤ max M K) := by
  have hval : (j : Fin n).val=j := by simp [Nat.mod_eq_of_lt hjn]
  unfold emittedDepth
  split_ifs with hdesc
  · have hb := hmax (j : Fin n)
    change atDepth d j ≤ h at hb
    constructor
    · omega
    · intro he
      have hh : backwardDepth d (j : Fin n)=h := by
        change atDepth d j=h
        omega
      have hh' := hpositions (j : Fin n) hh
      rw [hval] at hh'
      exact hh'.trans (le_max_left _ _)
  · have hb : prefixMinimum (atDepth d) (j-1) ≤ backwardDepth d 0 := by
      have hh := (prefix_minimum_le_iff (atDepth d) (j-1)
        (prefixMinimum (atDepth d) (j-1))).mp le_rfl 0 (by omega)
      exact hh
    constructor
    · omega
    · intro he
      have hp : ∀ i < j, h-1 ≤ atDepth d i := by
        have hh := (prefix_minimum_le_iff (atDepth d) (j-1) (h-1)).mp (by omega)
        intro i hi
        exact hh i (by omega)
      exact (hprefix j (by omega) hp).trans (le_max_right _ _)

/-- The loss from late prefix records is bounded by K, independently of n.
The other possible last event belongs to an original maximum-depth token. -/
theorem scan_deadline_of_prefix_bound (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h M K : ℕ) (hpos : 2 ≤ h)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i, backwardDepth d i=h → i.val ≤ M)
    (hprefix : ∀ j ≤ n,(∀ i < j,h-1 ≤ atDepth d i) → j ≤ K) :
    scanDeadline d ≤ (h-1)*(n-1)+max M K-1 := by
  have hqueue : queueDeadline (sweep d (n-1)) ≤ (n-1)*(h-2)+max M K := by
    unfold queueDeadline
    apply Finset.sup_le
    intro i _
    rw [first_lap_depth_formula hn d hi i]
    by_cases hi0 : i=0
    · subst i
      simp
    · simp only [ite_eq_right hi0]
      have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      have hb := emitted_depth_top_positions_prefix d h M K (by omega) hmax hhead hpositions hprefix
        i.val hip i.isLt
      by_cases hz : emittedDepth d i.val=0
      · simp only [ite_eq_left hz]
        omega
      · rw [ite_eq_right hz]
        by_cases ht : emittedDepth d i.val=h-1
        · rw [ht]
          have hj := hb.2 ht
          have he : h-1-1=h-2 := by omega
          rw [he]
          omega
        · have hh : emittedDepth d i.val ≤ h-2 := by omega
          have hmul := Nat.mul_le_mul_left (n-1) hh
          have he : emittedDepth d i.val-1+1=emittedDepth d i.val := by omega
          rw [← he,Nat.mul_add,Nat.mul_one] at hmul
          have hj := i.isLt
          omega
  have he : (n-1)+(n-1)*(h-2)=(h-1)*(n-1) := by
    have hh : h-2+1=h-1 := by omega
    calc
      _ = (h-2+1)*(n-1) := by ring
      _ = _ := by rw [hh]
  unfold scanDeadline
  omega


end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem aligned_anchor_prefix_gap_zero_word (p : State n) (a : Fin n)
    (hh : 2 ≤ height p a) (hn : 2 ≤ n)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (k : Fin n) (hgap : backwardDepth (displacement p a) k < height p a-1)
    (hfinish : k.val ≤ a.val+(-p a).val) :
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
  have hprefix : ∀ j ≤ n,(∀ i < j,h-1 ≤ atDepth d i) → j ≤ k.val := by
    intro j hj hp
    by_contra hnot
    have hk := hp k.val (by omega)
    have hk' : h-1 ≤ backwardDepth d k := by simpa only [atDepth,Fin.cast_val_eq_self] using hk
    change height p a-1 ≤ backwardDepth (displacement p a) k at hk'
    omega
  have ht := scan_deadline_of_prefix_bound hn d hinj h a.val k.val hh hmax hhead' hpositions hprefix
  have hbound : max a.val k.val ≤ a.val+(-p a).val := max_le (by omega) hfinish
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


#print axioms aligned_anchor_prefix_gap_zero_word
end LX.AnchoredPhases
