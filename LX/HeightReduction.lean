import LX.CompleteMapping

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem offset_difference_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, ((p i-i-(p a-a) : Fin n) : ℤ))=(n : ℤ)*height p a := by
  have hm := clockwise_representative_mass (permutation p a)
  simp_rw [clockwise_difference_value] at hm
  have he (i : Fin n) : permutation p a i-i=p i-i-(p a-a) := by
    change p i+(a-p a)-i=p i-i-(p a-a)
    abel
  simpa only [he,height] using hm

/-- If no anchor improves the odd half-size height, cyclic displacements must
be distinct. This derives the complete-mapping case from the actual height
obstruction instead of assuming a special input family. -/
theorem complete_of_minimum_height (p : State n) (h : ℕ) (hn : n=2*h+1)
    (hmin : ∀ a, h ≤ height p a) : CompleteMapping p := by
  intro a b hab
  by_contra hne
  let F := fun i j : Fin n => ((p j-j-(p i-i) : Fin n) : ℤ)
  have hpair (i j : Fin n) : F i j+F j i ≤ if i=j then 0 else (n : ℤ) := by
    by_cases hij : i=j
    · subst j
      simp [F]
    · rw [ite_eq_right hij]
      by_cases ho : p i-i=p j-j
      · simp [F,ho]
      · exact le_of_eq (LRX.AffineLift.cyclic_difference_sum (p i-i) (p j-j) ho)
  have hstrict : F a b+F b a < (if a=b then 0 else (n : ℤ)) := by
    rw [ite_eq_right hne]
    simp only [F,hab,sub_self,Fin.val_zero,Nat.cast_zero,zero_add]
    exact_mod_cast NeZero.pos n
  have hsumlt : (∑ i : Fin n, ∑ j : Fin n, (F i j+F j i)) <
      ∑ i : Fin n, ∑ j : Fin n, (if i=j then (0 : ℤ) else (n : ℤ)) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact Finset.sum_le_sum (fun j _ => hpair i j)
    · refine ⟨a,Finset.mem_univ _,?_⟩
      apply Finset.sum_lt_sum
      · intro j _
        exact hpair a j
      · exact ⟨b,Finset.mem_univ _,hstrict⟩
  have htranspose : (∑ i : Fin n, ∑ j : Fin n, F j i)=∑ i : Fin n, ∑ j : Fin n, F i j :=
    Finset.sum_comm
  have hsum : (∑ i : Fin n, ∑ j : Fin n, (F i j+F j i))=
      2*(n : ℤ)*(∑ i : Fin n, (height p i : ℤ)) := by
    simp only [Finset.sum_add_distrib]
    rw [htranspose]
    have hm (i : Fin n) : (∑ j : Fin n, F i j)=(n : ℤ)*height p i := offset_difference_mass p i
    simp_rw [hm]
    rw [← Finset.mul_sum]
    ring
  have hrow (i : Fin n) : (∑ j : Fin n, if i=j then (0 : ℤ) else (n : ℤ))=
      (n : ℤ)*((n : ℤ)-1) := by
    have he (j : Fin n) : (if i=j then (0 : ℤ) else (n : ℤ))=
        (n : ℤ)-(if j=i then (n : ℤ) else 0) := by
      by_cases hij : i=j
      · subst j
        simp
      · have hji : j≠i := Ne.symm hij
        simp [hij,hji]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring
  rw [hsum] at hsumlt
  simp_rw [hrow] at hsumlt
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsumlt
  have hlow : (n : ℤ)*h ≤ ∑ i : Fin n, (height p i : ℤ) := by
    calc
      _ = ∑ _i : Fin n, (h : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by exact_mod_cast hmin i)
  have hnp : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hna : (n : ℤ)=2*(h : ℤ)+1 := by exact_mod_cast hn
  have hprod := mul_le_mul_of_nonneg_left hlow (show (0 : ℤ) ≤ 2*n by positivity)
  have he : (n : ℤ)*((n : ℤ)*((n : ℤ)-1))=2*(n : ℤ)*((n : ℤ)*h) := by rw [hna]; ring
  rw [he] at hsumlt
  omega

/-- The odd maximal-height obstruction is completely paid. The remaining
height branches have an actual anchor at least one below half the dimension. -/
theorem odd_height_reduction (p : State n) (h : ℕ) (hn : n=2*h+1) (hn4 : 4 ≤ n) :
    (∃ a : Fin n, height p a < h) ∨
      ∃ w : List Letter, p*eval w=1 ∧
        4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases ha : ∃ a : Fin n, height p a < h
  · exact Or.inl ha
  · have hmin : ∀ a, h ≤ height p a := by
      intro a
      have hh : ¬ height p a < h := fun hh => ha ⟨a,hh⟩
      omega
    exact Or.inr (complete_mapping_upper_word p (complete_of_minimum_height p h hn hmin) hn4)

/-- Any remaining odd input has minimum anchor height exactly one or two
below half size. The maximal-height family and all smaller heights are paid.
The selected minimum-height anchor is not asserted to be majorized. -/
theorem odd_unpaid_height_cases (p : State n) (h : ℕ) (hn : n=2*h+1) (hn4 : 4 ≤ n)
    (hunpaid : ¬ ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n, (∀ b, height p a ≤ height p b) ∧
      (height p a+1=h ∨ height p a+2=h) := by
  have hex : ∃ b : Fin n, height p b < h :=
    (odd_height_reduction p h hn hn4).resolve_right hunpaid
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) (height p)
    ⟨0,Finset.mem_univ _⟩
  have hmin (b : Fin n) := ha b (Finset.mem_univ _)
  obtain ⟨b,hb⟩ := hex
  have hlt : height p a < h := lt_of_le_of_lt (hmin b) hb
  have hlow : ¬ height p a+3 ≤ h := by
    intro hbad
    obtain ⟨w,hw,hprice⟩ := low_height_word (by omega : 2 ≤ n) p a (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩
  exact ⟨a,hmin,by omega⟩

/-- The even case has the same two remaining relative heights. -/
theorem even_unpaid_height_cases (p : State n) (h : ℕ) (hn : n=2*h) (hn4 : 4 ≤ n)
    (hunpaid : ¬ ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n, (∀ b, height p a ≤ height p b) ∧
      (height p a+1=h ∨ height p a+2=h) := by
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) (height p)
    ⟨0,Finset.mem_univ _⟩
  have hmin (b : Fin n) := ha b (Finset.mem_univ _)
  obtain ⟨b,_,_,hb⟩ := exists_short_candidate p
  have hlt : height p a < h := by have := hmin b; omega
  have hlow : ¬ height p a+3 ≤ h := by
    intro hbad
    obtain ⟨w,hw,hprice⟩ := low_height_word (by omega : 2 ≤ n) p a (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩
  exact ⟨a,hmin,by omega⟩

#print axioms complete_of_minimum_height
#print axioms odd_height_reduction
#print axioms odd_unpaid_height_cases
#print axioms even_unpaid_height_cases
end LX.AnchoredPhases
