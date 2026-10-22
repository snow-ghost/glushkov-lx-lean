import LX.EvenUnpaidRankPeak

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_fixed_gap_exact_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 0 < height p a)
    (hf : (fixedPositions (permutation p a)).card ≤ (a-p a).val+1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*(((a-p a).val : ℤ)+1-anchorReserve p a) := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count (displacement p a) (height p a) hh
  rw [top_depth_count_eq_fixed] at hr
  let T := height p a*(n-1)+(a-p a).val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)=0 := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+((a-p a).val : ℤ) := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  nlinarith

/-- A fixed window contains 128 distinct actual offsets. Their existence
and separation follow from the proved predecessor bound, not enumeration. -/
theorem terminal_window_samples (p : State n) (hn : 4096 < n)
    (hpred : ∀ r : Fin n,∃ b : Fin n,(r-(p b-b)).val < 23) :
    ∃ S : Finset (Fin n),S.card=128 ∧ S ⊆ rawOffsets p ∧
      ∀ t ∈ S,40 ≤ (-t).val ∧ (-t).val ≤ 2983 := by
  classical
  let r := fun j : Fin 128 => -((40+23*j.val : ℕ) : Fin n)
  choose b hb using fun j : Fin 128 => hpred (r j)
  have hgap (j : Fin 128) : (b j-p (b j)).val=
      40+23*j.val+(r j-(p (b j)-b j)).val := by
    have hj := j.isLt
    have he : b j-p (b j)=((40+23*j.val : ℕ) : Fin n)+(r j-(p (b j)-b j)) := by
      dsimp only [r]
      ring
    have hv : ((40+23*j.val : ℕ) : Fin n).val=40+23*j.val := by
      exact Nat.mod_eq_of_lt (by omega : 40+23*j.val < n)
    rw [he,Fin.val_add,hv,Nat.mod_eq_of_lt (by have := hb j; omega)]
  have hi : Function.Injective (fun j => p (b j)-b j) := by
    intro i j hij
    have he : b i-p (b i)=b j-p (b j) := by linear_combination -hij
    have hv := congrArg Fin.val he
    rw [hgap i,hgap j] at hv
    have hbi := hb i
    have hbj := hb j
    exact Fin.ext (by omega)
  let S := Finset.univ.image (fun j => p (b j)-b j)
  refine ⟨S,?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  · intro t ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨b j,Finset.mem_univ _,rfl⟩
  · intro t ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    rw [show -(p (b j)-b j)=b j-p (b j) by ring,hgap]
    have hj := j.isLt
    have hbj := hb j
    constructor <;> omega

/-- Terminal offsets of an unpaid input are neither low phases nor forward
arrows at the next height, apart from the explicit head offset. -/
theorem even_terminal_next_height_backward (p : State n) (m : ℕ)
    (hn : n=2*m) (hnlarge : 4096 < n)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ 12)
    (hdepth : ∀ b,depthCount (displacement p b) (height p b-1) ≤ 36)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8192)
    (b : Fin n) (hglo : 40 ≤ (b-p b).val) (hghi : (b-p b).val ≤ 2983) :
    height p b+1 ≠ m ∧
      (height p b=m → p 0 ≠ p b-b →
        ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c=p b-b) := by
  constructor
  · intro hh
    obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega)
      (by have := hF b; omega)
    have hr := anchor_reserve_nonneg p b
    have hg : ((b-p b).val : ℤ) ≤ 2983 := by exact_mod_cast hghi
    exact hunpaid ⟨w,hw,by linarith⟩
  · intro hh hhead
    obtain ⟨c,hraw,hheight,_,hlast⟩ := last_offset_source p b
    have hgap : (c-p c).val=(b-p b).val := by
      congr 1
      linear_combination -hraw
    have hcount : depthCount (displacement p c) (height p c-1) ≤ c.val+(-p c).val := by
      have hc := hdepth c
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    refine ⟨c,?_,by omega,hraw⟩
    rw [mem_descendingPositions]
    by_contra hnot
    have hforward : c.val < (p c).val := by
      by_contra hnot'
      have he : p c=c := Fin.ext (by omega)
      rw [he,sub_self,Fin.val_zero] at hgap
      omega
    obtain ⟨w,hw,hprice⟩ := even_higher_anchor_reserve_price p c (by omega) (by omega)
      (fun he => hhead (he.trans hraw)) hlast hcount
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    have hg' : (c-p c).val=c.val+n-(p c).val := by
      rw [Nat.add_comm c.val n]
      exact Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)
    have hfinish : c.val+(-p c).val ≤ 2983 := by rw [hneg]; omega
    have hr := anchor_reserve_nonneg p c
    exact hunpaid ⟨w,hw,by omega⟩

#print axioms even_fixed_gap_exact_word
#print axioms terminal_window_samples
#print axioms even_terminal_next_height_backward
end LX.AnchoredPhases
