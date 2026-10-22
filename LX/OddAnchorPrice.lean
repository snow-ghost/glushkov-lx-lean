import LX.CrowdedDeadline

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- The anchor realizes the largest backward depth, not just the minimum displacement. -/
theorem anchor_depth_eq_height (p : State n) (a : Fin n) :
    backwardDepth (displacement p a) a=height p a := by
  have hh := (candidate_price_components p a).2 a
  have hnonneg : 0 ≤ displacement p a a+(backwardDepth (displacement p a) a : ℤ) := by
    rw [displacement_add_depth (is_lift p a)]
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [displacement_anchor] at hnonneg
  omega

theorem odd_unique_max_depth (p : State n) (a : Fin n)
    (hm : LRX.AffineLift.Majorized (displacement p a))
    (hn : n=2*height p a+1) (i : Fin n)
    (hi : backwardDepth (displacement p a) i=height p a) : i=a := by
  have hmax (j : Fin n) : backwardDepth (displacement p a) j ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 j
  have hc := top_depth_count (is_lift p a) hm (height p a) (by omega) hmax
  have hcard : (Finset.univ.filter (fun j => height p a ≤ backwardDepth (displacement p a) j)).card ≤ 1 := by
    change depthCount (displacement p a) (height p a) ≤ 1
    omega
  apply (Finset.card_le_one.mp hcard) i (by simp [hi]) a
  simp [anchor_depth_eq_height]

/-- In the odd maximal-height case, an anchor with enough forward displacement
pays the requested negative linear term. All price premises are derived from
this actual input permutation and its majorized anchored lift. -/
theorem odd_forward_anchor_zero_word (p : State n) (a : Fin n) (r : ℕ)
    (hm : LRX.AffineLift.Majorized (displacement p a))
    (hn : n=2*height p a+1) (hh : 2 ≤ height p a)
    (ha : 0 < a.val) (hforward : a.val+height p a ≤ (p a).val+r)
    (hcorner : 5 ≤ a.val+(n-(p a).val)) :
    ∃ w : List Letter, p*eval w=1 ∧ (∀ i,run w (displacement p a) i=0) ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+5+4*r := by
  let h := height p a
  have hn2 : 2 ≤ n := by omega
  have hd := is_lift p a
  have hl (i : Fin n) : labels (displacement p a) i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using LRX.AffineLift.lift_residue hd i
  have hinj : Function.Injective (labels (displacement p a)) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ h := by
    exact_mod_cast (candidate_price_components p a).2 i
  have hhead : backwardDepth (displacement p a) 0 < h := by
    have hle := hmax 0
    by_contra hnot
    have he := odd_unique_max_depth p a hm hn 0 (by omega)
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  have hpositions (i : Fin n) (hi : backwardDepth (displacement p a) i=h) : i.val ≤ a.val := by
    rw [odd_unique_max_depth p a hm hn i hi]
  have htime := majorized_scan_deadline hn2 hd hm hinj h a.val hh (by omega)
    hmax hhead hpositions
  have hslack : 3*(n-2*h)+2=5 := by dsimp [h]; omega
  rw [hslack] at htime
  let T := (h-1)*(n-1)+(a.val-1)+(n-(p a).val)
  have hT : scanDeadline (displacement p a) ≤ T := by
    dsimp only [T]
    have hp := (p a).isLt
    have hm' := le_max_left a.val 5
    have hm'' := le_max_right a.val 5
    have he : max a.val 5=a.val ∨ max a.val 5=5 := max_choice _ _
    rcases he with he | he <;> rw [he] at htime <;> omega
  have hcast : (T : Fin n)=(phase p a : Fin n) := by
    have hn0 : 1 ≤ n := by omega
    have hh0 : 1 ≤ h := by dsimp [h]; omega
    dsimp only [T,phase,h]
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub hh0,Nat.cast_sub hn0,Nat.cast_sub ha,Nat.cast_sub (Nat.le_of_lt (p a).isLt)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,
      Int.cast_sub,Int.cast_natCast]
    ring
  obtain ⟨w,ht,_⟩ := candidate_sorting_word hn2 p a
  obtain ⟨v,hv,hzero,hvl⟩ := ht.word_at_cursor_zero hn2 p (phase p a : Fin n) hd.1 hinj hl T
    ((ht.rotations_le_deadline hn2 hd.1 hinj).trans hT)
  rw [hcast,sub_self,Fin.val_zero,add_zero] at hvl
  refine ⟨v,hv,hzero,?_⟩
  have hx := (candidate_price_components p a).1
  have hna : (n : ℤ)=2*(height p a : ℤ)+1 := by exact_mod_cast hn
  have hTa : (T : ℤ)=((height p a : ℤ)-1)*((n : ℤ)-1)+
      ((a.val : ℤ)-1)+((n : ℤ)-(p a).val) := by
    dsimp only [T,h]
    push_cast [Nat.cast_sub (by omega : 1 ≤ height p a),Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub ha,Nat.cast_sub (Nat.le_of_lt (p a).isLt)]
    rfl
  have hforward' : (a.val : ℤ)+height p a ≤ (p a).val+r := by exact_mod_cast hforward
  have hvl' : (v.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hvl
  nlinarith

theorem odd_forward_anchor_word (p : State n) (a : Fin n) (r : ℕ)
    (hm : LRX.AffineLift.Majorized (displacement p a))
    (hn : n=2*height p a+1) (hh : 2 ≤ height p a)
    (ha : 0 < a.val) (hforward : a.val+height p a ≤ (p a).val+r)
    (hcorner : 5 ≤ a.val+(n-(p a).val)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+5+4*r := by
  obtain ⟨w,hw,_,hprice⟩ := odd_forward_anchor_zero_word p a r hm hn hh ha hforward hcorner
  exact ⟨w,hw,hprice⟩

#print axioms odd_unique_max_depth
#print axioms odd_forward_anchor_zero_word
#print axioms odd_forward_anchor_word
end LX.AnchoredPhases
