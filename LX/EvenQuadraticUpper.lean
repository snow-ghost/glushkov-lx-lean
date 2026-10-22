import LX.EvenTerminalWindow

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A literal word with the requested quadratic and linear terms for every
even size. The constant 8192 is uniform in n and in the input permutation. -/
theorem even_quadratic_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8192 := by
  classical
  by_contra hunpaid
  have hunpaid32 : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by linarith⟩
  have hnlarge : 4096 < n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ) ≤ 4096 := by omega
    linarith
  obtain ⟨a,ha,hh,hrank,hheights,hF,hdepth,hdesc,hpred,_,hhigh⟩ :=
    even_unpaid_bounded_rank_geometry hn4 p m hn hunpaid32
  let Q := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  let Bad := Q.image (fun t => p a-a+t)
  have hBad : Bad.card ≤ 58 := (Finset.card_image_le).trans hhigh
  have hbad (b : Fin n) (hb : height p a+2 ≤ height p b) : p b-b ∈ Bad := by
    apply Finset.mem_image.mpr
    refine ⟨cyclicOffset p a b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · have he := reanchor_height p a b
      unfold rankSurplus
      omega
    · unfold cyclicOffset
      ring
  let Dlow := (descendingPositions p).filter fun b => height p b=height p a
  let Dhigh := (descendingPositions p).filter fun b => height p b=m
  have hlowCount : m ≤ Dlow.card+37 := by
    have hmin (b : Fin n) : height p a ≤ height p b := (hheights b).1
    have hlo := even_minimum_anchor_count p a hmin (by omega)
    rw [zero_surplus_count_eq_minimum_offsets p a hmin] at hlo
    have hhi := even_unpaid_minimum_offset_low_arrow_count p (height p a) 11 12
      hheights hF (by omega) (by omega) hunpaid32
    change (minimumHeightOffsets p (height p a)).card ≤ Dlow.card+11+2*12+2 at hhi
    omega
  obtain ⟨S,hScard,hSraw,hSgap⟩ := terminal_window_samples p hnlarge hpred
  let V := Dhigh.image (fun b => p b-b)
  have hsub : S ⊆ (Bad ∪ {p 0}) ∪ V := by
    intro t ht
    by_cases hb : t ∈ Bad ∪ {p 0}
    · exact Finset.mem_union_left _ hb
    have hnbad : t ∉ Bad := fun h => hb (Finset.mem_union_left _ h)
    have hnhead : t ≠ p 0 := by intro he; apply hb; simp [he]
    obtain ⟨b,_,hbt⟩ := Finset.mem_image.mp (hSraw ht)
    have hgap : (b-p b).val=(-t).val := by rw [← hbt]; congr 1; ring
    have htBounds := hSgap t ht
    have hterminal := even_terminal_next_height_backward p m hn hnlarge hF hdepth hunpaid b
      (by omega) (by omega)
    have hhb : height p b=m := by
      have hbmin := (hheights b).1
      have hbhigh : ¬ height p a+2 ≤ height p b := by
        intro h
        exact hnbad (hbt ▸ hbad b h)
      omega
    obtain ⟨c,hc,hch,hcr⟩ := hterminal.2 hhb (by
      intro he
      exact hnhead (hbt.symm.trans he.symm))
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hch⟩,hcr.trans hbt⟩
  have hlargeCount : 69 ≤ Dhigh.card := by
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ {p 0}) V)
    have hb := Finset.card_union_le Bad {p 0}
    have hv : V.card ≤ Dhigh.card := Finset.card_image_le
    simp only [Finset.card_singleton] at hb
    omega
  have hdisjoint : Disjoint Dlow Dhigh := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    omega
  have hsubset : Dlow ∪ Dhigh ⊆ descendingPositions p := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hb).1
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint] at hc
  omega

#print axioms even_quadratic_upper_word
end LX.AnchoredPhases

namespace LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing

/-- The requested rational diameter estimate, proved for every even n >= 4. -/
theorem even_diameter_quadratic_upper (n : ℕ) [NeZero n] (hn4 : 4 ≤ n)
    (heven : Even n) :
    (diameter n : ℚ) < (3*(n : ℚ)^2-8*n)/4+8192 := by
  obtain ⟨m,hm⟩ := heven
  apply (diameter_lt_iff_words (by omega : 2 ≤ n) _).mpr
  intro p
  obtain ⟨w,hw,hprice⟩ := AnchoredPhases.even_quadratic_upper_word hn4 p⁻¹ m (by omega)
  refine ⟨w,(inv_mul_eq_one.mp hw).symm,?_⟩
  have hq : 4*(w.length : ℚ) < 3*(n : ℚ)^2-8*n+4*8192 := by exact_mod_cast hprice
  linarith

#print axioms even_diameter_quadratic_upper
end LX
