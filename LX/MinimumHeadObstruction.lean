import LX.EvenBinaryRankObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem equal_raw_offset_height (p : State n) (a b : Fin n)
    (he : p a-a=p b-b) : height p a=height p b := by
  have hp : permutation p a=permutation p b := by
    apply Equiv.ext
    intro i
    change p i+(a-p a)=p i+(b-p b)
    linear_combination -he
  simp only [height,hp]

/-- If the head is not a minimum phase, the offset count loses another
position. This conclusion holds in both parity cases. -/
theorem unpaid_minimum_count_without_head (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e)
    (hhead : height p 0 ≠ height p a) :
    (minimumRawOffsets p (height p a)).card ≤ height p a := by
  classical
  let M := minimumRawOffsets p (height p a)
  have hheadnot : p 0 ∉ M := by
    intro ht
    obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets p (height p a) (p 0)).mp ht
    have he := equal_raw_offset_height p b 0 (by simpa using hraw)
    exact hhead (he.symm.trans hb)
  change M.card ≤ height p a
  by_cases hz : (0 : Fin n) ∈ M
  · obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets p (height p a) 0).mp hz
    have hpb : p b=b := sub_eq_zero.mp hraw
    have heq : permutation p b=p := by ext i; simp [permutation,hpb]
    change (descendingPositions (permutation p b)).card=height p a at hb
    rw [heq] at hb
    let D := (descendingPositions p).erase (p.symm 0)
    let V := D.image (fun i => p i-i)
    have hsub : M ⊆ insert 0 V := by
      intro t ht
      by_cases ht0 : t=0
      · simp [ht0]
      obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
      have hth : t ≠ p 0 := by intro heq; exact hheadnot (heq ▸ ht)
      obtain ⟨i,hi,hpi,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid
        (by rwa [hct]) (by rwa [hct])
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr
        ⟨(fun hi0 => hpi (by rw [hi0,Equiv.apply_symm_apply])),hi⟩,hrawi.trans hct⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hv : V.card ≤ D.card := Finset.card_image_le
    have hp0 : p 0 ≠ 0 := by intro heq; exact hheadnot (heq.symm ▸ hz)
    have hpre : p.symm 0 ≠ 0 := by
      intro heq
      have he' := congrArg p heq
      simp only [Equiv.apply_symm_apply] at he'
      exact hp0 he'.symm
    have hmem : p.symm 0 ∈ descendingPositions p := by
      rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
      exact Fin.pos_iff_ne_zero.mpr hpre
    have hd : D.card=height p a-1 := by dsimp only [D]; rw [Finset.card_erase_of_mem hmem,hb]
    omega
  let S := Finset.univ.filter fun b : Fin n => height p b=height p a
  have hS : S.Nonempty := ⟨a,by simp [S]⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S (fun b => (p b-b).val) hS
  have hbh : height p b=height p a := (Finset.mem_filter.mp hb).2
  let D := lowerOffsetDrops p (p b-b)
  let V := D.image (fun i => p i-i)
  have hsub : M ⊆ insert (p b-b) V := by
    intro t ht
    by_cases htb : t=p b-b
    · simp [htb]
    obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p (height p a) t).mp ht
    have ht0 : t ≠ 0 := by intro heq; exact hz (heq ▸ ht)
    have hth : t ≠ p 0 := by intro heq; exact hheadnot (heq ▸ ht)
    obtain ⟨i,hi,_,hrawi⟩ := minimum_unpaid_positive_backward p a c e he hn hh hmin hc hunpaid
      (by rwa [hct]) (by rwa [hct])
    have hcle := hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
    have hne : (p c-c).val ≠ (p b-b).val := by
      intro heq
      exact htb (hct.symm.trans (Fin.ext heq))
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,by rw [hrawi]; omega⟩,hrawi.trans hct⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd := lower_offset_drop_bound p b
  have hp0 : p 0 ≠ p b-b := by
    intro heq
    exact hheadnot ((mem_minimum_raw_offsets _ _ _).mpr ⟨b,hbh,heq.symm⟩)
  rw [hbh,ite_eq_right hp0] at hd
  change D.card+1 ≤ height p a at hd
  omega

/-- Every remaining even input has its initial position in a minimum
phase. This follows from the sharp count, without a global-energy premise. -/
theorem even_unpaid_head_minimum (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : height p 0=height p a := by
  by_contra hnot
  have hc := unpaid_minimum_count_without_head p a 0 (by omega) (by omega) hh hmin
    (by simpa using hunpaid) hnot
  have hz := zero_surplus_count_le_minimum_offsets p a hmin
  have hl := even_minimum_anchor_count p a hmin hn
  omega

#print axioms unpaid_minimum_count_without_head
#print axioms even_unpaid_head_minimum
end LX.AnchoredPhases
