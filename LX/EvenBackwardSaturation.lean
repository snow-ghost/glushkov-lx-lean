import LX.MinimumHeadObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_unpaid_minimum_count_exact (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (minimumRawOffsets p (height p a)).card=height p a+1 := by
  have hu := unpaid_minimum_offset_count p a 0 (by omega) (by omega) hh hmin (by simpa using hunpaid)
  have hz := zero_surplus_count_le_minimum_offsets p a hmin
  have hl := even_minimum_anchor_count p a hmin hn
  omega

/-- The exact minimum-offset count exhausts all ordinary backward arrows
with positive images. Consequently every such arrow has minimum height. -/
theorem even_unpaid_positive_backward_minimum (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12)
    (k : Fin n) (hk : k ∈ descendingPositions p) (hpk : p k ≠ 0) :
    height p k=height p a := by
  classical
  by_contra hnot
  let M := minimumRawOffsets p (height p a)
  let D := ((descendingPositions p).erase k).erase (p.symm 0)
  let V := D.image (fun i => p i-i)
  have hcard : M.card=height p a+1 := even_unpaid_minimum_count_exact p a hn hh hmin hunpaid
  have hcover (t : Fin n) (ht : t ∈ M) (ht0 : t ≠ 0) (hth : t ≠ p 0) : t ∈ V := by
    obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets _ _ _).mp ht
    obtain ⟨i,hi,hpi,hit⟩ := minimum_unpaid_positive_backward p a b 0 (by omega) (by omega)
      hh hmin hb (by simpa using hunpaid) (by rwa [hbt]) (by rwa [hbt])
    have hih : height p i=height p a := (equal_raw_offset_height p i b hit).trans hb
    have hik : i ≠ k := by intro he; rw [he] at hih; exact hnot hih
    have hi0 : i ≠ p.symm 0 := by intro he; apply hpi; rw [he,Equiv.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi0,Finset.mem_erase.mpr ⟨hik,hi⟩⟩,hit.trans hbt⟩
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd0 : D.card ≤ (descendingPositions p).card-1 := by
    have hc := Finset.card_le_card (Finset.erase_subset (p.symm 0) ((descendingPositions p).erase k))
    rw [Finset.card_erase_of_mem hk] at hc
    exact hc
  have hhead := even_unpaid_head_minimum p a hn hh hmin hunpaid
  by_cases hp0 : p 0=0
  · have heq : permutation p 0=p := by ext i; simp [permutation,hp0]
    change (descendingPositions (permutation p 0)).card=height p a at hhead
    rw [heq] at hhead
    have hs : M ⊆ insert 0 V := by
      intro t ht
      by_cases ht0 : t=0
      · simp [ht0]
      exact Finset.mem_insert_of_mem (hcover t ht ht0 (by rwa [hp0]))
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    omega
  have hj0 : p.symm 0 ≠ 0 := by
    intro he
    have he' := congrArg p he
    simp only [Equiv.apply_symm_apply] at he'
    exact hp0 he'.symm
  have hjd : p.symm 0 ∈ descendingPositions p := by
    rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr hj0
  have hjk : p.symm 0 ≠ k := by
    intro he
    apply hpk
    rw [← he,Equiv.apply_symm_apply]
  have hd : D.card=(descendingPositions p).card-2 := by
    dsimp only [D]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjk,hjd⟩),Finset.card_erase_of_mem hk]
    omega
  by_cases hz : (0 : Fin n) ∈ M
  · obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets _ _ _).mp hz
    have hpb : p b=b := sub_eq_zero.mp hraw
    have heq : permutation p b=p := by ext i; simp [permutation,hpb]
    change (descendingPositions (permutation p b)).card=height p a at hb
    rw [heq] at hb
    have hs : M ⊆ V ∪ {0,p 0} := by
      intro t ht
      by_cases ht0 : t=0
      · exact Finset.mem_union_right _ (by simp [ht0])
      by_cases hth : t=p 0
      · exact Finset.mem_union_right _ (by simp [hth])
      exact Finset.mem_union_left _ (hcover t ht ht0 hth)
    have hc := (Finset.card_le_card hs).trans (Finset.card_union_le V {0,p 0})
    have hp := Finset.card_pair_eq_one_or_two (a := (0 : Fin n)) (b := p 0)
    omega
  · have hs : M ⊆ insert (p 0) V := by
      intro t ht
      by_cases hth : t=p 0
      · simp [hth]
      have ht0 : t ≠ 0 := by intro he; exact hz (he ▸ ht)
      exact Finset.mem_insert_of_mem (hcover t ht ht0 hth)
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
    have hb := rank_peak_descending_count p a 1 hR
    omega

#print axioms even_unpaid_minimum_count_exact
#print axioms even_unpaid_positive_backward_minimum
end LX.AnchoredPhases
