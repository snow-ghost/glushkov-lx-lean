import LX.SaturatedMinimumPhases

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem odd_unpaid_global_height_cases {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m+1) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    height p a=m ∨ height p a+1=m := by
  have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
  rw [displacement_anchor] at hh
  by_contra hnot
  have hlow : 2*height p a+5 ≤ n := by omega
  obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a hlow
  exact hunpaid ⟨w,hw,by linarith⟩

theorem odd_unpaid_all_global_fixed_cases (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a : Fin n,GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) (a : Fin n) :
    (height p a=m ∧ (fixedPositions (permutation p a)).card=1) ∨
      (height p a+1=m ∧ (fixedPositions (permutation p a)).card=3) := by
  have hh := odd_unpaid_global_height_cases hn4 m hn (hall a) hunpaid
  have hf := saturated_of_all_anchors_global p hall a
  omega

/-- Consecutive occupied offsets in the all-global family are separated by
half the sum of their multiplicities. In the unpaid odd case the gap is at
most three. -/
theorem odd_all_global_next_gap (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a : Fin n,GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) (a : Fin n) :
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t ≤ 3 ∧ t < n ∧
      p b-b=p a-a+(t : Fin n) ∧
      2*t=(fixedPositions (permutation p a)).card+(fixedPositions (permutation p b)).card := by
  have ha := odd_unpaid_all_global_fixed_cases hn4 p m hn hall hunpaid a
  obtain ⟨b,t,ht,htn,hoff,hheight,_⟩ := next_occupied_phase p a (by omega)
  have hb := odd_unpaid_all_global_fixed_cases hn4 p m hn hall hunpaid b
  have hfa := saturated_of_all_anchors_global p hall a
  have hfb := saturated_of_all_anchors_global p hall b
  exact ⟨b,t,ht,by omega,htn,hoff,by omega⟩

/-- Every target residue has an occupied predecessor at distance at most
two, retaining the minimizing property needed to exclude internal holes. -/
theorem odd_all_global_predecessor (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a : Fin n,GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) (r : Fin n) :
    ∃ a : Fin n,(r-(p a-a)).val ≤ 2 ∧
      ∀ b : Fin n,(r-(p a-a)).val ≤ (r-(p b-b)).val := by
  obtain ⟨a,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun a => (r-(p a-a)).val) ⟨0,Finset.mem_univ _⟩
  refine ⟨a,?_,fun b => hmin b (Finset.mem_univ _)⟩
  by_contra hnot
  obtain ⟨b,t,ht,ht3,htn,hoff,_⟩ := odd_all_global_next_gap hn4 p m hn hall hunpaid a
  have htv : (t : Fin n).val=t := by simp [Nat.mod_eq_of_lt htn]
  have hle : (t : Fin n) ≤ r-(p a-a) := by change (t : Fin n).val ≤ _; rw [htv]; omega
  have he : r-(p b-b)=r-(p a-a)-(t : Fin n) := by rw [hoff]; ring
  have hnear := hmin b (Finset.mem_univ _)
  rw [he,Fin.coe_sub_iff_le.mpr hle,htv] at hnear
  omega

theorem raw_offset_mass (p : State n) :
    (∑ i : Fin n,((p i-i : Fin n) : ℤ))=(n : ℤ)*(descendingPositions p).card := by
  have h := clockwise_representative_mass p
  simpa only [clockwise_difference_value] using h

/-- The ordinary number of backward arrows is bounded even when raw offset
zero is unoccupied. A maximal raw offset and saturation give the bound. -/
theorem odd_all_global_descending_bound (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a : Fin n,GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (descendingPositions p).card ≤ m+1 := by
  classical
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => (p i-i).val) ⟨0,Finset.mem_univ _⟩
  let F := fixedPositions (permutation p a)
  have hf := saturated_of_all_anchors_global p hall a
  have hh := odd_unpaid_global_height_cases hn4 m hn (hall a) hunpaid
  have hFl : F.card ≤ n := (Finset.card_le_univ F).trans_eq (Fintype.card_fin n)
  have hfilter : Finset.univ.filter (fun i : Fin n => (p i-i).val < (p a-a).val)=Fᶜ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    have hm := hmax i (Finset.mem_univ _)
    have he : i ∈ F ↔ p i-i=p a-a := by
      rw [mem_fixedPositions,← offset_zero_iff_source_fixed]
      exact sub_eq_zero
    rw [he,Fin.ext_iff]
    omega
  have hsum := cyclic_offset_mass p a
  have heq (i : Fin n) : (cyclicOffset p a i : ℤ)=
      ((p i-i : Fin n) : ℤ)-((p a-a : Fin n) : ℤ)+
        if (p i-i).val < (p a-a).val then (n : ℤ) else 0 :=
    cyclic_subtraction_value (p i-i) (p a-a)
  simp_rw [heq] at hsum
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,raw_offset_mass] at hsum
  have hif : (∑ i : Fin n,if (p i-i).val < (p a-a).val then (n : ℤ) else 0)=
      (n : ℤ)*((n : ℤ)-F.card) := by
    rw [← Finset.sum_filter,hfilter]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_compl,Fintype.card_fin,
      Nat.cast_sub hFl]
    ring
  rw [hif] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hsat : (n : ℤ)=2*(height p a : ℤ)+F.card := by
    have hp : 0 < F.card := Finset.card_pos.mpr
      ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
    change F.card=n-2*height p a at hf
    omega
  have hnpos : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hidentity : ((descendingPositions p).card : ℤ)=(p a-a).val-height p a := by
    nlinarith
  have hr := (p a-a).isLt
  omega

#print axioms odd_all_global_next_gap
#print axioms odd_all_global_predecessor
#print axioms odd_all_global_descending_bound
end LX.AnchoredPhases
