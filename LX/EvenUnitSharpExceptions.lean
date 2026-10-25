import LX.FiberDepthGeometry
import LX.PrefixGapDeadline
import LX.RankPeakCount
import LX.RankPeakReserve
import LX.ReflectionPhases
import LX.ReserveAwareAnchorPrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The two exceptional adjacent perturbations of the even reflection at
zero are paid using the actual early prefix, rather than total crowding. -/
theorem even_unit_sharp_exception (p : State n) (a u : Fin n)
    (ha : GlobalMinimum p a) (m : ℕ) (hn : n=2*m) (hm : 4 ≤ m)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i= -i)
    (hu : u.val=1 ∨ u.val=m+1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  classical
  obtain ⟨hah,hares⟩ := even_unit_reserve_height m hn ha hunit
  have hR (t : Fin n) : rankSurplus p a t.val ≤ 1 := by
    have hb := critical_rank_peak_reserve p a t ha 0 (by omega)
    rw [hares] at hb
    norm_num at hb
    by_contra hnot
    have ht : 2 ≤ rankSurplus p a t.val := by omega
    nlinarith only [hb,ht,sq_nonneg (rankSurplus p a t.val-1)]
  have hmin (b : Fin n) : height p a ≤ height p b := by
    have := (even_unit_all_anchor_bounds m hn ha hunit b).1
    omega
  have hF (b : Fin n) : (fixedPositions (permutation p b)).card ≤ 2 :=
    (rank_peak_anchor_bounds p a 1 hmin hR).2 b
  have hmem (b i : Fin n) : i ∈ fixedPositions (permutation p b) ↔ p i-i=p b-b := by
    simp only [mem_fixedPositions,← offset_zero_iff_source_fixed,cyclicOffset,sub_eq_zero]
  have hv1 : (1 : Fin n).val=1 := by norm_num [Nat.mod_eq_of_lt (by omega : 1<n)]
  have hv2 : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2<n)]
  have hv3 : (3 : Fin n).val=3 := by norm_num [Nat.mod_eq_of_lt (by omega : 3<n)]
  have hv4 : (4 : Fin n).val=4 := by norm_num [Nat.mod_eq_of_lt (by omega : 4<n)]
  have huv : (u+1).val=u.val+1 := Fin.val_add_one_of_lt' (by rcases hu with h | h <;> omega)
  have hdouble : (m : Fin n)+(m : Fin n)=0 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    simp only [Nat.cast_mul,Nat.cast_ofNat,Fin.natCast_self] at he
    linear_combination -he
  have htwou : u+u=2 := by
    rcases hu with h | h
    · have he : u=1 := Fin.ext (by omega)
      rw [he]
      ring
    · have he : u=(m : Fin n)+1 := by
        apply Fin.ext
        change u.val=(m%n+1%n)%n
        rw [Nat.mod_eq_of_lt (by omega : m<n),Nat.mod_eq_of_lt (by omega : 1<n),Nat.mod_eq_of_lt (by omega)]
        omega
      rw [he]
      linear_combination hdouble
  have hpu : p u= -(u+1) := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_right] using hp (u+1)
  have hpv : p (u+1)= -u := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left] using hp u
  have hother (j : Fin n) (hju : j ≠ u) (hjv : j ≠ u+1) : p j= -j := by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hju hjv] using hp j
  have hrawu : p u-u= -3 := by rw [hpu]; linear_combination -htwou
  have hrawv : p (u+1)-(u+1)= -3 := by rw [hpv]; linear_combination -htwou
  have hfueq : (fixedPositions (permutation p u)).card=2 := by
    have hsub : ({u,u+1} : Finset (Fin n)) ⊆ fixedPositions (permutation p u) := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact (hmem u i).mpr (by rw [hi])
      · exact (hmem u i).mpr (by rw [hi,hrawv,hrawu])
    have hc := Finset.card_le_card hsub
    have hne : u ≠ u+1 := by intro he; have := congrArg Fin.val he; omega
    rw [Finset.card_pair hne] at hc
    have := hF u
    omega
  have hhu : height p u=height p a := by
    have hh := rank_peak_fixed_count p a 1 hR u
    rw [hfueq] at hh
    have := hmin u
    omega
  rcases hu with hu | hu
  · have huone : u=1 := Fin.ext (by omega)
    have hv : u+1=(2 : Fin n) := Fin.ext (by omega)
    have hrawc : p (2 : Fin n)-(2 : Fin n)=p u-u := by rw [← hv,hrawv,hrawu]
    have hpc : p (2 : Fin n)= -(1 : Fin n) := by rw [← hv,hpv,huone]
    have hhc : height p (2 : Fin n)=height p a := by
      have he : permutation p (2 : Fin n)=permutation p u := by
        apply Equiv.ext
        intro i
        change p i+(2-p 2)=p i+(u-p u)
        linear_combination -hrawc
      have hh := congrArg (fun q : State n => (descendingPositions q).card) he
      change height p (2 : Fin n)=height p u at hh
      omega
    have hfiber (i : Fin n) (hi : p i-i=p (2 : Fin n)-2) : i=1 ∨ i=2 := by
      by_cases hiu : i=u
      · exact Or.inl (hiu.trans huone)
      by_cases hiv : i=u+1
      · exact Or.inr (hiv.trans hv)
      have hraw : p i-i= -(3 : Fin n) := hi.trans (hrawc.trans hrawu)
      rw [hother i hiu hiv] at hraw
      have he : Even (3 : Fin n) := by
        refine ⟨i,?_⟩
        linear_combination hraw
      have he' := (Fin.even_iff_mod_of_even (show Even n from ⟨m,by omega⟩)).mp he
      rw [hv3] at he'
      norm_num at he'
    have hhead : p 0 ≠ p (2 : Fin n)-2 := by
      intro he
      have hc := hfiber 0 (by simpa using he)
      rcases hc with he | he <;> have := congrArg Fin.val he <;> simp only [Fin.val_zero] at this <;> omega
    have hlast (i : Fin n) (hi : p i-i=p (2 : Fin n)-2) : i.val ≤ (2 : Fin n).val := by
      rcases hfiber i hi with rfl | rfl <;> omega
    have hgap : backwardDepth (displacement p (2 : Fin n)) (3 : Fin n) < height p (2 : Fin n)-1 := by
      by_contra hnot
      have hw := displacement_depth_width_bound (is_lift p (2 : Fin n))
        (fun i j => (displacement_strict_width p (2 : Fin n) i j).le)
        (height p (2 : Fin n)-1) (3 : Fin n) (by omega)
      rw [show height p (2 : Fin n)-1+1=height p (2 : Fin n) by omega,
        displacement_offset,top_depth_count_eq_fixed] at hw
      have hf := hF (2 : Fin n)
      have hp3 : p (3 : Fin n)= -(3 : Fin n) := hother 3 (by intro he; have := congrArg Fin.val he; omega)
        (by intro he; have := congrArg Fin.val he; omega)
      have hoff : cyclicOffset p (2 : Fin n) (3 : Fin n)= -(3 : Fin n) := by
        unfold cyclicOffset
        rw [hp3,hpc]
        ring
      have hvneg : (-(3 : Fin n)).val=n-3 := by
        rw [Fin.val_neg,ite_eq_right (by intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega),hv3]
      rw [hoff] at hw
      change (((-(3 : Fin n)).val : ℕ) : ℤ) - _ + _ ≤ _ at hw
      rw [hvneg] at hw
      omega
    have hfinish : (2 : Fin n).val+(-p (2 : Fin n)).val=3 := by rw [hpc,neg_neg,hv1,hv2]
    obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p (2 : Fin n)
      (by omega) (by omega) hhead hlast (3 : Fin n) hgap (by omega)
    have hcap := (candidate_price_components p (2 : Fin n)).1
    have hn' : (n : ℤ)=2*(height p (2 : Fin n) : ℤ)+2 := by omega
    have hfinish' : ((2 : Fin n).val : ℤ)+((-p (2 : Fin n)).val : ℤ)=3 := by exact_mod_cast hfinish
    exact ⟨w,hw,by nlinarith only [hprice,hcap,hn',hfinish']⟩
  · have hcu : (2 : Fin n) ≠ u := by intro he; have := congrArg Fin.val he; omega
    have hcv : (2 : Fin n) ≠ u+1 := by intro he; have := congrArg Fin.val he; omega
    have hpc : p (2 : Fin n)= -(2 : Fin n) := hother 2 hcu hcv
    have hrawc : p (2 : Fin n)-2= -(4 : Fin n) := by rw [hpc]; ring
    have hfiber (i : Fin n) (hi : p i-i=p (2 : Fin n)-2) : i=2 := by
      have hiu : i ≠ u := by
        intro he
        rw [he,hrawu,hrawc] at hi
        have h31 : (3 : Fin n)=(4 : Fin n) := neg_injective hi
        have := congrArg Fin.val h31
        omega
      have hiv : i ≠ u+1 := by
        intro he
        rw [he,hrawv,hrawc] at hi
        have h31 : (3 : Fin n)=(4 : Fin n) := neg_injective hi
        have := congrArg Fin.val h31
        omega
      rw [hother i hiu hiv,hrawc] at hi
      have htwice : i+i=(2 : Fin n)+(2 : Fin n) := by linear_combination -hi
      have hc := doubled_residue_cases i 2 htwice
      have hi' := i.isLt
      have hiv' : i.val ≠ (u+1).val := fun he => hiv (Fin.ext he)
      apply Fin.ext
      omega
    have hfc : (fixedPositions (permutation p (2 : Fin n))).card=1 := by
      have he : fixedPositions (permutation p (2 : Fin n))={(2 : Fin n)} := by
        ext i
        rw [hmem,Finset.mem_singleton]
        exact ⟨hfiber i,fun he => he ▸ rfl⟩
      rw [he,Finset.card_singleton]
    have hoff : cyclicOffset p u (2 : Fin n)= -(1 : Fin n) := by
      unfold cyclicOffset
      rw [hrawc,hrawu]
      ring
    have hval : (cyclicOffset p u (2 : Fin n)).val=n-1 := by
      rw [hoff,Fin.val_neg,ite_eq_right (by intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega),hv1]
    have hcount := below_count_succ p u (cyclicOffset p u (2 : Fin n)).val
    rw [offset_fiber_count,hfc,hval,show n-1+1=n by omega] at hcount
    have htotal : belowCount p u n=n := by
      have he : (Finset.univ.filter fun i : Fin n => (cyclicOffset p u i).val<n)=Finset.univ :=
        Finset.filter_true_of_mem (fun i _ => (cyclicOffset p u i).isLt)
      unfold belowCount
      rw [he,Finset.card_univ,Fintype.card_fin]
    rw [htotal] at hcount
    have hhc : height p (2 : Fin n)=height p a := by
      have hh := reanchor_height p u (2 : Fin n)
      rw [hval] at hh
      omega
    have hhead : p 0 ≠ p (2 : Fin n)-2 := by
      intro he
      have he' := hfiber 0 (by simpa using he)
      have := congrArg Fin.val he'
      simp only [Fin.val_zero] at this
      omega
    have hlast (i : Fin n) (hi : p i-i=p (2 : Fin n)-2) : i.val ≤ (2 : Fin n).val := by rw [hfiber i hi]
    have hd := rank_peak_next_depth_fiber p a 1 hR (2 : Fin n) (by omega)
    rw [hfc] at hd
    have hfinish : (2 : Fin n).val+(-p (2 : Fin n)).val=4 := by rw [hpc,neg_neg,hv2]
    obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p (2 : Fin n) (by omega) (by omega)
      hhead hlast (by omega)
    have hr := anchor_reserve_nonneg p (2 : Fin n)
    have hf : ((2 : Fin n).val : ℤ)+((-p (2 : Fin n)).val : ℤ)=4 := by exact_mod_cast hfinish
    exact ⟨w,hw,by omega⟩

#print axioms even_unit_sharp_exception
end LX.AnchoredPhases
