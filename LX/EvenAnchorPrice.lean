import LX.EvenSecondReserve
import LX.EvenSecondHeight

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Equal raw offsets give literally the same normalized permutation and
displacement vector, hence preserve global minimality. -/
theorem same_offset_global_minimum {p : State n} {a b : Fin n}
    (ha : GlobalMinimum p a) (he : p b-b=p a-a) : GlobalMinimum p b := by
  have hshift : b-p b=a-p a := by linear_combination -he
  have hperm : permutation p b=permutation p a := by
    apply Equiv.ext
    intro i
    change p i+(b-p b)=p i+(a-p a)
    rw [hshift]
  have hh : height p b=height p a := by simp only [height,hperm]
  have hd : displacement p b=displacement p a := by
    funext i
    simp only [displacement,hperm,hh]
  intro c d hcd
  rw [hd]
  exact ha c d hcd

/-- Select the last physical position carrying a given minimum-phase
offset. This bounds all maximum-depth positions of that phase. -/
theorem last_same_offset_anchor {p : State n} {a : Fin n} (ha : GlobalMinimum p a) :
    ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=p a-a ∧
      ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val := by
  classical
  let F := Finset.univ.filter (fun i : Fin n => p i-i=p a-a)
  have hF : F.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  let b := F.max' hF
  have hb : p b-b=p a-a := (Finset.mem_filter.mp (Finset.max'_mem F hF)).2
  refine ⟨b,same_offset_global_minimum ha hb,hb,?_⟩
  intro i hi
  exact Finset.le_max' F i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.trans hb⟩)

/-- A raw offset of minus k aligns the final orientation after either k
or n+k rotations measured from the chosen anchor. -/
theorem negative_offset_finish (p : State n) (a : Fin n) (k : ℕ) (hk : k < n)
    (he : p a-a= -(k : Fin n)) :
    a.val+(-p a).val=k ∨ a.val+(-p a).val=n+k := by
  have hneg : -p a=(k : Fin n)-a := by linear_combination -he
  have hkv : (k : Fin n).val=k := by simp [Nat.mod_eq_of_lt hk]
  rw [hneg]
  by_cases ha : a ≤ (k : Fin n)
  · rw [Fin.coe_sub_iff_le.mpr ha,hkv]
    have ha' : a.val ≤ k := by simpa only [Fin.le_def,hkv] using ha
    exact Or.inl (by omega)
  · have ha' : (k : Fin n) < a := lt_of_not_ge ha
    rw [Fin.coe_sub_iff_lt.mpr ha',hkv]
    have hai := a.isLt
    exact Or.inr (by omega)

/-- The even maximal-height price needs only a last-in-fiber anchor and
the final-orientation bound; the input need not be a reflection. -/
theorem maximal_even_anchor_word {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hcorner : 8 ≤ a.val+(-p a).val) (R : ℕ)
    (hfinish : a.val+(-p a).val ≤ n+R) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+4*((R : ℤ)+1) := by
  let h := height p a
  have hn2 : 2 ≤ n := by omega
  have hap : 0 < a.val := by
    by_contra hnot
    have he : a=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    exact hhead (by simp [he])
  have hd := is_lift p a
  have hl (i : Fin n) : labels (displacement p a) i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hinj : Function.Injective (labels (displacement p a)) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ h := by
    exact_mod_cast (candidate_price_components p a).2 i
  have hhead' : backwardDepth (displacement p a) 0 < h := by
    apply head_reserve_of_distinct_offset
    intro he
    apply hhead
    simpa only [cyclicOffset,sub_zero,sub_eq_zero] using he
  have hpositions (i : Fin n) (hi : backwardDepth (displacement p a) i=h) : i.val ≤ a.val := by
    have hd' := maximum_depth_displacement hd i (by intro j; rw [hi]; exact hmax j)
    rw [hi,displacement_offset] at hd'
    have hval : (cyclicOffset p a i).val=0 := by omega
    have he : cyclicOffset p a i=0 := Fin.ext hval
    apply hlast
    exact sub_eq_zero.mp he
  have ht := majorized_scan_deadline hn2 hd (global_minimum_majorized ha) hinj h a.val hh
    (by omega) hmax hhead' hpositions
  have hcount : 3*(n-2*h)+2=8 := by dsimp [h]; omega
  rw [hcount] at ht
  have hbound : max a.val 8 ≤ a.val+(-p a).val := max_le (by omega) hcorner
  let T := (h-1)*(n-1)+(a.val-1)+(-p a).val
  have hT : scanDeadline (displacement p a) ≤ T := by dsimp only [T]; omega
  have hcast : (T : Fin n)=(phase p a : Fin n) := by
    dsimp only [T,phase,h]
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ height p a),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  obtain ⟨w,htw,_⟩ := candidate_sorting_word hn2 p a
  obtain ⟨v,hv,hlen⟩ := htw.word_at_cursor hn2 p (phase p a : Fin n) hd.1 hinj hl T
    ((htw.rotations_le_deadline hn2 hd.1 hinj).trans hT)
  rw [hcast,sub_self,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=((h : ℤ)-1)*((n : ℤ)-1)+(a.val : ℤ)-1+((-p a).val : ℤ) := by
    dsimp only [T]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h),Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hap]
    ring
  have hx := (candidate_price_components p a).1
  have hlen' : (v.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hn' : (n : ℤ)=2*(h : ℤ)+2 := by exact_mod_cast hn
  have hf : (a.val : ℤ)+((-p a).val : ℤ) ≤ (n : ℤ)+R := by exact_mod_cast hfinish
  exact ⟨v,hv,by dsimp only [h] at *; nlinarith⟩

#print axioms maximal_even_anchor_word
end LX.AnchoredPhases
